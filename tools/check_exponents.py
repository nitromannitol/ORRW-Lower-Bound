"""Compare every exponent in a paper statement with those in its Lean statement.

The exponents `1/(d+1)`, `d/(d+1)`, `(d-1)/(d+1)`, `(d-1)/d`, `1+1/d`, `2/d`,
`1+2/d` and `-d/2` carry the content of this paper, and two of them differ by a
transposition that no type error would catch.  So they are compared directly:
every exponent is extracted from the paper's statement and from the frozen Lean
statement and the two multisets are matched.

Three kinds of difference are expected and are recorded per node rather than
silently ignored:

  notation   the paper writes `\\gamma`, Lean writes `γ`
  general    the paper writes the `d = 2` case as `2/3` and `1/3`; Lean carries
             the general `d/(d+1)` and `1/(d+1)`, which agree at `d = 2`
  split      `thm:return` is one theorem in the paper and three nodes here, so
             each node sees the whole theorem's line range but carries only its
             own display

    python3 tools/check_exponents.py
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_exponents.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"


def paper_path() -> Path:
    env = os.environ.get("ORRW_PAPER")
    return Path(env) if env else ROOT / "paper" / "orrw.tex"


# Superscripts that are not exponents of a quantity: set names like `ℤ^d`, the
# inverse in `Δ^{-1}`, the summation limits, and the `θ`-expressions of lem:exp,
# which Lean writes with `Real.exp` rather than with `^`.
NOISE = {"d", "c", "M", "R", "+", "-1", "2", "\\Z", "m+h-1", "n-1",
         "\\gamma", "\\theta\\zeta/2", "2\\thetab", "-\\thetas/2"}

# Per node: exponents present in the paper's line range but legitimately absent
# from this node's Lean statement, with the reason.
EXPECTED_ABSENT: dict[str, dict[str, str]] = {
    "lem-exp": {
        "\\theta(N\\wedge\\zeta)/2":
            "notation: Lean uses Real.exp (theta * (zeta N w : Real) / 2); "
            "zeta N w represents N wedge zeta (F-604, F-605)",
    },
    "prop-beta-sharp": {"-\\gamma": "notation: Lean writes the same exponent as -γ"},
    "thm-occupation": {
        "1/3": "general: the paper's d = 2 case; Lean carries 1/(d+1)",
        "2/3": "general: the paper's d = 2 case; Lean carries d/(d+1)",
        "-d/(d+1)": "split: belongs to the eq:cesaro display, node thm-occupation-cesaro",
    },
    "thm-occupation-cesaro": {
        "1/3": "general: the paper's d = 2 case, in a sibling node",
        "2/3": "general: the paper's d = 2 case, in a sibling node",
        "1/(d+1)": "rearrangement: paper bounds the sum; Lean bounds its average, see VERIFICATION.md",
        "d/(d+1)": "weaker beta dependence: Lean simplifies the paper coefficient to C beta, see VERIFICATION.md",
    },
}


def balanced(s: str, i: int, op: str, cl: str) -> str | None:
    depth = 0
    for j in range(i, len(s)):
        if s[j] == op:
            depth += 1
        elif s[j] == cl:
            depth -= 1
            if depth == 0:
                return s[i + 1:j]
    return None


def paper_exponents(seg: str) -> set[str]:
    out = []
    for m in re.finditer(r"\^", seg):
        i = m.end()
        if i >= len(seg):
            continue
        if seg[i] == "{":
            g = balanced(seg, i, "{", "}")
            if g is not None:
                out.append(g)
        else:
            out.append(seg[i])
    cleaned = {re.sub(r"\s|\\,|\\!|\\bigl|\\bigr", "", e) for e in out}
    def fraction(m):
        num, den = m.groups()
        if not re.fullmatch(r"[A-Za-z0-9]+", num):
            num = "(" + num + ")"
        if not re.fullmatch(r"[A-Za-z0-9]+", den):
            den = "(" + den + ")"
        return num + "/" + den
    cleaned = {re.sub(r"\\(?:d?frac|tfrac)\{([^{}]+)\}\{([^{}]+)\}", fraction, e)
               for e in cleaned}
    return cleaned - NOISE


def lean_exponents(blk: str) -> set[str]:
    out = []
    for m in re.finditer(r"\^\s*", blk):
        i = m.end()
        if i >= len(blk):
            continue
        if blk[i] == "(":
            g = balanced(blk, i, "(", ")")
            if g is not None:
                out.append(g)
        else:
            g = re.match(r"[A-Za-zγβ0-9]+", blk[i:])
            if g:
                out.append(g.group(0))
    cleaned = set()
    for e in out:
        e = re.sub(r"\(\s*([a-zA-Zβγ])\s*:\s*ℝ\s*\)", r"\1", e)
        e = re.sub(r"\(\s*(\d+)\s*:\s*ℝ\s*\)", r"\1", e)
        e = re.sub(r"\s+", "", e)
        if e.startswith("-(") and e.endswith(")"):
            e = "-" + e[2:-1]
        cleaned.add(e)
    return cleaned - {"2"}


def main() -> int:
    lines = paper_path().read_text(encoding="utf-8").splitlines()
    manifest = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))
    unexplained: list[tuple[str, list[str]]] = []
    compared = 0

    for node in manifest.get("nodes") or []:
        rng = re.search(r"orrw\.tex:(\d+)-(\d+)", node["source"])
        if not rng:
            continue
        a, b = int(rng.group(1)), int(rng.group(2))
        seg = "\n".join(lines[a - 1:b])
        text = (ROOT / node["file"]).read_text(encoding="utf-8")
        blk = text[text.index("-- FROZEN-STATEMENT-BEGIN"):
                   text.index("-- FROZEN-STATEMENT-END")]
        pe, le = paper_exponents(seg), lean_exponents(blk)
        compared += 1
        allowed = EXPECTED_ABSENT.get(node["id"], {})
        missing = [e for e in sorted(pe) if e not in le and e not in allowed]
        print(f"  {node['id']:24s} paper {sorted(pe)}")
        print(f"  {'':24s} lean  {sorted(le)}")
        for e in sorted(pe):
            if e in allowed:
                print(f"  {'':24s}   {e}: {allowed[e]}")
        if missing:
            unexplained.append((node["id"], missing))

    if unexplained:
        print("\ncheck_exponents: a paper exponent has no counterpart in Lean:",
              file=sys.stderr)
        for nid, ms in unexplained:
            print(f"  {nid}: {', '.join(ms)}", file=sys.stderr)
        return 1
    print(f"\ncheck_exponents: OK ({compared} statements; every paper exponent "
          f"appears in its Lean statement or is explained above)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
