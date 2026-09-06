#!/usr/bin/env python3
"""Axiom-closure gate for the frozen manifest.

`check_manifest.py` counts `sorry` tokens per file.  That is not enough: a file
can contain no `sorry` and still depend on one transitively, through an import
of another node that is still a draft.  `ORRW.Frozen.insertion_inequality` was
exactly that -- zero `sorry`s of its own, `sorryAx` in its axiom closure.

A node may be SEALED only if `#print axioms` on its export shows no `sorryAx`.
This runs Lean and is the authority; the token count is only a fast prefilter.

Usage: check_axioms.py [--emit]   (--emit rewrites `state:` in the manifest)
"""
import io, os, re, subprocess, sys, tempfile, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
man = io.open(ROOT / "ledger/manifest.yaml", encoding="utf-8").read()
nodes = []
for b in man.split("  - id: ")[1:]:
    nodes.append((b.split("\n")[0].strip(),
                  re.search(r"file: (\S+)", b).group(1),
                  re.search(r"export: (\S+)", b).group(1)))

mods = sorted({f[:-5].replace("/", ".") for _, f, _ in nodes})
src = "".join(f"import {m}\n" for m in mods) + \
      "".join(f"#print axioms {e}\n" for _, _, e in nodes)
# The probe has to live inside the package for `lake env lean` to resolve
# its imports.  A fresh clone has no `scratch/`, so make it.
(ROOT / "scratch").mkdir(exist_ok=True)
with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT / "scratch",
                                 delete=False) as fh:
    fh.write(src); tmp = fh.name
try:
    r = subprocess.run(["lake", "env", "lean", tmp], cwd=ROOT, capture_output=True,
                       text=True, timeout=3600,
                       env={**os.environ,
                            "PATH": os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"]})
finally:
    os.unlink(tmp)

axioms = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", r.stdout))
clean, dirty, missing = [], [], []
for nid, _, exp in nodes:
    ax = axioms.get(exp)
    if ax is None:
        missing.append(nid)
    elif "sorryAx" in ax:
        dirty.append(nid)
    else:
        clean.append(nid)

for nid in clean:   print("  clean   %s" % nid)
for nid in dirty:   print("  sorryAx %s   <- NOT proved, however few `sorry`s its file has" % nid)
for nid in missing: print("  ??      %s   (no axiom line; did it elaborate?)" % nid)

if "--emit" in sys.argv:
    out, head = [], man.split("  - id: ")[0]
    for b in man.split("  - id: ")[1:]:
        nid = b.split("\n")[0].strip()
        f = re.search(r"file: (\S+)", b).group(1)
        own = re.search(r"\bsorry\b", io.open(ROOT / f, encoding="utf-8").read())
        # SEALED: axiom-clean.  CONDITIONAL: a proof is written, but it leans on a
        # node that is still a draft, so `sorryAx` is in its closure.  DRAFT_SORRY:
        # no proof yet.
        st = "SEALED" if nid in clean else ("DRAFT_SORRY" if own else "CONDITIONAL")
        out.append(re.sub(r"state: \w+", "state: " + st, b))
    io.open(ROOT / "ledger/manifest.yaml", "w", encoding="utf-8").write(
        head + "".join("  - id: " + b for b in out))
    print("\nmanifest states rewritten from the axiom closure")

print("\n%d clean, %d depend on sorryAx, %d unresolved" % (len(clean), len(dirty), len(missing)))
sys.exit(1 if dirty and "--emit" not in sys.argv else 0)
