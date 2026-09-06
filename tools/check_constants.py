"""Check that every constant depends only on the dimension.

The paper's constants are always "depending only on `d`".  In Lean that is a
property of quantifier order: the existential must be bound before `β` and
before `n`.  Writing

    theorem foo {d : ℕ} (hd : 2 ≤ d) {β : ℝ} (hβ : 1 ≤ β) : ∃ c, ... β ... n ...

reads as `∀ β, ∃ c(β)`, which lets the constant absorb any power of `β` and
makes a factor like `β^{-d/(d+1)}` decorative -- the statement would hold with
the wrong exponent.  That is a silent weakening, invisible to every other check
here, so it gets its own.

The rule enforced: in a frozen statement that binds a real-valued existential,
none of `β`, `n`, `k`, `m`, `h` may be a *parameter* of the theorem; they must be
quantified inside the conclusion, after the existential.  Only `d` may be a
parameter, which is what the paper's own convention allows: "`c > 0` and
`C < ∞` are constants that depend only on `d` ... They never depend on `β`, `k`,
`m`, or `n`."

    python3 tools/check_constants.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_constants.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"

# Names that must never be theorem parameters when a constant is existential.
FORBIDDEN = ("β", "n", "k", "m", "h")

# Only a real-valued existential is a *constant*.  `lem-walk-order` also binds
# an existential -- the ordering of the visited sites -- and that one must depend
# on the word and the time, so it is not what this check is about.
CONSTANT = re.compile(r"∃\s+[^,:]*:\s*ℝ")


def split_statement(block: str) -> tuple[str, str]:
    """(binders, conclusion), split at the FIRST `:` outside every bracket.

    Every theorem parameter is bracketed, so its own `:` sits at depth one or
    more; the first `:` at depth zero is the one that ends the binder list.
    Taking the last such `:` instead would cut inside `∃ c : ℝ` and hide the
    existential in the binders, which is precisely the thing being looked for."""
    depth = 0
    for i, ch in enumerate(block):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and not block.startswith(":=", i):
            return block[:i], block[i + 1:]
    return block, ""


def parameters(binders: str) -> set[str]:
    """Variable names bound as theorem parameters."""
    names: set[str] = set()
    for m in re.finditer(r"[({\[]([^:()\[\]{}]+):", binders):
        for tok in m.group(1).split():
            names.add(tok)
    return names


def main() -> int:
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
    bad, ok = [], 0
    print(f"{'node':28s} {'real constant?':15s} {'bad parameters':22s}")
    for node in manifest.get("nodes") or []:
        text = (ROOT / node["file"]).read_text(encoding="utf-8")
        blk = text[text.index("-- FROZEN-STATEMENT-BEGIN") + len("-- FROZEN-STATEMENT-BEGIN"):
                   text.index("-- FROZEN-STATEMENT-END")]
        binders, concl = split_statement(blk)
        has_exists = bool(CONSTANT.search(concl))
        params = parameters(binders)
        offenders = sorted(params & set(FORBIDDEN))
        mark = ""
        if has_exists and offenders:
            bad.append((node["id"], offenders))
            mark = "  <-- CONSTANT MAY DEPEND ON " + ", ".join(offenders)
        else:
            ok += 1
        print(f"  {node['id']:26s} {'yes' if has_exists else 'no':13s} "
              f"{', '.join(offenders) if offenders else '-':20s}{mark}")

    if bad:
        print("\ncheck_constants: a constant is bound after a quantity it must not "
              "depend on:", file=sys.stderr)
        for nid, off in bad:
            print(f"  {nid}: move {', '.join(off)} inside the existential", file=sys.stderr)
        return 1
    print(f"\ncheck_constants: OK ({ok} statements; every existential constant is "
          f"bound before β, n, k, m and h, so it can depend only on d)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
