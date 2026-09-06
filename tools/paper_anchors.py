#!/usr/bin/env python3
"""Check (or repair) the paper line ranges recorded in ledger/manifest.yaml.

Each manifest node names the paper statement it formalizes as

    source: orrw.tex:<a>-<b> (label <lab>[, ...])

The line range is derived data: it is the span of the LaTeX environment that
contains `\\label{<lab>}`.  Editing the paper anywhere above a statement shifts
that span, so the recorded range goes stale silently.  The label itself is
stable, so this tool recomputes every range from its label and reports drift.

    python3 tools/paper_anchors.py            # check, exit 1 on drift
    python3 tools/paper_anchors.py --fix      # rewrite the stale source: lines

Nodes whose `source:` names no paper label (the model guards) are skipped.
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("paper_anchors.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"
def _paper_path() -> Path:
    """The paper: the copy pinned in this repository, or `$ORRW_PAPER`."""
    env = os.environ.get("ORRW_PAPER")
    return Path(env) if env else ROOT / "paper" / "orrw.tex"


PAPER = _paper_path()

SOURCE_RE = re.compile(r"^orrw\.tex:(?P<a>\d+)-(?P<b>\d+)\s*(?P<rest>.*)$")
LABEL_RE = re.compile(r"label\s+([A-Za-z][A-Za-z0-9:_-]*)")
BEGIN_RE = re.compile(r"\\begin\{([A-Za-z*]+)\}")
END_RE = re.compile(r"\\end\{([A-Za-z*]+)\}")

# Environments that carry a statement we would ever anchor to.
ANCHORABLE = {
    "theorem", "lemma", "proposition", "corollary", "definition", "problem",
    "equation", "equation*", "align", "align*", "gather", "gather*",
}


def span_of_label(lines: list[str], label: str) -> tuple[int, int]:
    """1-indexed inclusive span of the environment containing \\label{label}."""
    marker = f"\\label{{{label}}}"
    hits = [i for i, line in enumerate(lines) if marker in line]
    if len(hits) != 1:
        raise LookupError(f"label {label!r} occurs {len(hits)} times, want 1")
    at = hits[0]

    # Walk up to the innermost enclosing anchorable \begin, tracking depth so a
    # nested environment that closes above us is not mistaken for our opener.
    depth = 0
    start = None
    for i in range(at, -1, -1):
        for env in END_RE.findall(lines[i]):
            if i != at and env in ANCHORABLE:
                depth += 1
        for env in BEGIN_RE.findall(lines[i]):
            if env not in ANCHORABLE:
                continue
            if depth:
                depth -= 1
            else:
                start = (i, env)
                break
        if start:
            break
    if start is None:
        raise LookupError(f"label {label!r} is not inside an anchorable environment")

    i0, env = start
    depth = 0
    for j in range(i0 + 1, len(lines)):
        if re.search(rf"\\begin\{{{re.escape(env)}\}}", lines[j]):
            depth += 1
        if re.search(rf"\\end\{{{re.escape(env)}\}}", lines[j]):
            if depth:
                depth -= 1
            else:
                return i0 + 1, j + 1
    raise LookupError(f"environment {env} opened at line {i0 + 1} never closes")


def main() -> int:
    fix = "--fix" in sys.argv[1:]
    if not PAPER.exists():
        print(f"paper_anchors: paper not found at {PAPER}", file=sys.stderr)
        return 2
    lines = PAPER.read_text(encoding="utf-8").splitlines()
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))

    drift: list[tuple[str, str, str]] = []
    skipped = 0
    checked = 0
    for node in manifest.get("nodes") or []:
        nid, source = node["id"], node["source"]
        label_match = LABEL_RE.search(source)
        if not label_match:
            skipped += 1
            continue
        label = label_match.group(1)
        try:
            a, b = span_of_label(lines, label)
        except LookupError as exc:
            drift.append((nid, source, f"UNRESOLVABLE: {exc}"))
            continue
        checked += 1
        want = f"orrw.tex:{a}-{b}"
        got = SOURCE_RE.match(source)
        if got and (int(got.group("a")), int(got.group("b"))) == (a, b):
            continue
        rest = got.group("rest") if got else source[source.find("("):]
        drift.append((nid, source, f"{want} {rest}".strip()))

    if not drift:
        print(f"paper_anchors: OK ({checked} anchors resolved, "
              f"{skipped} nodes carry no paper label)")
        return 0

    for nid, old, new in drift:
        print(f"  {nid}\n    was: {old}\n    now: {new}")

    if not fix:
        print(f"\npaper_anchors: {len(drift)} stale anchor(s); rerun with --fix",
              file=sys.stderr)
        return 1

    text = MANIFEST.read_text(encoding="utf-8")
    for nid, old, new in drift:
        if new.startswith("UNRESOLVABLE"):
            print(f"paper_anchors: cannot repair {nid}", file=sys.stderr)
            return 1
        before = f"    source: {old}\n"
        if before not in text:
            print(f"paper_anchors: no verbatim source line for {nid}", file=sys.stderr)
            return 1
        text = text.replace(before, f"    source: {new}\n", 1)
    MANIFEST.write_text(text, encoding="utf-8")
    print(f"\npaper_anchors: repaired {len(drift)} anchor(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
