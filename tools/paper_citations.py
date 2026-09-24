"""Check (or repair) the `orrw.tex:<a>-<b>` citations inside the Lean sources.

The docstrings point at the paper by line range.  Line ranges are derived data:
inserting a paragraph anywhere above a statement shifts every citation below it,
silently.  A citation that also names the LaTeX `\\label` can be recomputed, so
this tool resolves those and repairs them.  A citation with no nearby label
points into the middle of a proof and cannot be resolved mechanically; those are
listed so they can be checked by hand or dropped.

    python3 tools/paper_citations.py           # check, exit 1 if a resolvable
                                               # citation is stale
    python3 tools/paper_citations.py --fix     # repair the resolvable ones
    python3 tools/paper_citations.py --list-unanchored
"""

from __future__ import annotations

import importlib.util
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
def _paper_path() -> Path:
    """The paper: the copy pinned in this repository, or `$ORRW_PAPER`."""
    env = os.environ.get("ORRW_PAPER")
    return Path(env) if env else ROOT / "paper" / "orrw.tex"


PAPER = _paper_path()

_spec = importlib.util.spec_from_file_location("pa", ROOT / "tools" / "paper_anchors.py")
_pa = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_pa)

CITE_RE = re.compile(r"orrw\.tex:(\d+)(?:-(\d+))?")
# A frozen file opens with a header docstring naming the paper statement it
# transcribes: its LaTeX label and its line range.  Three wordings are in use
# (citation before the label, after it, or with another backticked token
# between), so rather than match a wording, take the whole leading `/- ... -/`
# block: it names exactly one primary label, and the citation in it is that
# statement's.  A citation anywhere else in the file points into a proof and is
# left alone -- re-anchoring it from a nearby label would silently retarget it.
HEADER_LABEL_RE = re.compile(r"label\s+`([A-Za-z][A-Za-z0-9:_-]*)`")


def header_block(text: str) -> tuple[int, int] | None:
    """Offsets of the leading `/- ... -/` docstring, if the file opens with one."""
    if not text.startswith("/-"):
        return None
    end = text.find("-/")
    return (0, end) if end > 0 else None


def main() -> int:
    fix = "--fix" in sys.argv[1:]
    list_unanchored = "--list-unanchored" in sys.argv[1:]
    lines = PAPER.read_text(encoding="utf-8").splitlines()

    stale, ok, unanchored, unresolvable = [], 0, [], []
    for path in sorted((ROOT / "ORRW").rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        # Only a frozen file's PRIMARY anchor is repaired: the first citation in
        # its header docstring, sitting beside the label it names.  Later
        # citations in the same header point at other passages, and a Support
        # file's header deliberately cites a whole section, so neither is
        # resolvable from a statement's span.
        block = header_block(text) if str(path).startswith(str(ROOT / "ORRW" / "Frozen")) else None
        primary_label, primary_at = None, None
        if block:
            lab = HEADER_LABEL_RE.search(text[block[0]:block[1]])
            cite = CITE_RE.search(text[block[0]:block[1]])
            if lab and cite and abs(lab.start() - cite.start()) <= 120:
                primary_label, primary_at = lab.group(1), cite.start()
        out, cursor, changed = [], 0, False
        for m in CITE_RE.finditer(text):
            out.append(text[cursor:m.start()])
            cursor = m.end()
            label = primary_label if m.start() == primary_at else None
            if label is None:
                unanchored.append((path, text[:m.start()].count("\n") + 1, m.group(0)))
                out.append(m.group(0))
                continue
            try:
                a, b = _pa.span_of_label(lines, label)
            except LookupError as exc:
                unresolvable.append((path, m.group(0), label, str(exc)))
                out.append(m.group(0))
                continue
            want = f"orrw.tex:{a}-{b}"
            if want == m.group(0):
                ok += 1
                out.append(m.group(0))
            else:
                stale.append((path, text[:m.start()].count("\n") + 1,
                              m.group(0), want, label))
                out.append(want)
                changed = True
        out.append(text[cursor:])
        if changed and fix:
            path.write_text("".join(out), encoding="utf-8")

    print(f"paper_citations: {ok} correct, {len(stale)} stale, "
          f"{len(unanchored)} not anchored to a label, "
          f"{len(unresolvable)} unresolvable")

    for path, line, got, want, label in stale:
        print(f"  {path.relative_to(ROOT)}:{line}  {got} -> {want}  (label {label})")
    for path, got, label, why in unresolvable:
        print(f"  {path.relative_to(ROOT)}  {got}: {why}")

    if list_unanchored:
        print("\nCitations with no label to anchor them (each points into a proof;\n"
              "verify by hand or drop the line numbers and keep the prose):")
        for path, line, got in unanchored:
            print(f"  {path.relative_to(ROOT)}:{line}  {got}")

    if unresolvable:
        return 1
    if stale and not fix:
        print("\npaper_citations: rerun with --fix to repair the resolvable ones",
              file=sys.stderr)
        return 1
    if stale and fix:
        print(f"\npaper_citations: repaired {len(stale)} citation(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
