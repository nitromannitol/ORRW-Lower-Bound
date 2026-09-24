"""Check that every theorem-like statement in the paper is represented in the manifest.

The manifest says which paper statement each Lean node transcribes.  This asks
the complementary question, which no other checker asks: is there a statement in
the paper that no node claims?  A formalization can be entirely axiom-clean and
still be silently incomplete, so the gap is worth a gate of its own.

Open problems (the `problem` environment of Section 9) are excluded: they are
questions, not claims.

    python3 tools/check_coverage.py
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_coverage.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"
def _paper_path() -> Path:
    """The paper: the copy pinned in this repository, or `$ORRW_PAPER`."""
    env = os.environ.get("ORRW_PAPER")
    return Path(env) if env else ROOT / "paper" / "orrw.tex"


PAPER = _paper_path()

STATEMENT_ENVS = ("theorem", "lemma", "proposition", "corollary")
LABEL_IN_STATEMENT = re.compile(
    r"\\begin\{(" + "|".join(STATEMENT_ENVS) + r")\}(?:\[[^\]]*\])?[^\\]*\\label\{([^}]+)\}")
LABEL_TOKEN = re.compile(r"\b((?:thm|lem|prop|cor|eq):[A-Za-z0-9:_-]+)")


def main() -> int:
    if not PAPER.exists():
        print(f"check_coverage: paper not found at {PAPER}", file=sys.stderr)
        return 2
    text = PAPER.read_text(encoding="utf-8")
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))

    claimed: set[str] = set()
    for node in manifest.get("nodes") or []:
        claimed |= set(LABEL_TOKEN.findall(node["source"]))

    statements = []
    seen = set()
    for m in LABEL_IN_STATEMENT.finditer(text):
        if m.group(2) not in seen:
            seen.add(m.group(2))
            statements.append((m.group(1), m.group(2), text[:m.start()].count("\n") + 1))

    uncovered = [(k, lab, ln) for k, lab, ln in statements if lab not in claimed]

    print(f"check_coverage: {len(statements)} statements in the paper, "
          f"{len(statements) - len(uncovered)} represented in the manifest")
    if uncovered:
        print("\nNot claimed by any manifest node:")
        for kind, lab, ln in uncovered:
            print(f"  orrw.tex:{ln}  {kind} {lab}")
        print("\ncheck_coverage: the formalization does not cover the whole paper",
              file=sys.stderr)
        return 1
    print("every theorem, lemma and proposition in the paper is represented in the manifest")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
