#!/usr/bin/env python3
"""Require successful Lean output for every export, using only standard axioms.

With --emit, mark successfully checked nodes SEALED; preserve PROVED states.
No manifest is written if Lean fails or any export is missing or uses another axiom.
"""
import os
import pathlib
import re
import subprocess
import sys
import tempfile

from axiom_audit import audit

ROOT = pathlib.Path(__file__).resolve().parent.parent


def main():
    man = (ROOT / "ledger/manifest.yaml").read_text()
    blocks = man.split("  - id: ")
    nodes = [(b.split("\n")[0].strip(), re.search(r"file: (\S+)", b).group(1),
              re.search(r"export: (\S+)", b).group(1)) for b in blocks[1:]]
    mods = sorted({f[:-5].replace("/", ".") for _, f, _ in nodes})
    src = "".join(f"import {m}\n" for m in mods)
    src += "".join(f"#print axioms {e}\n" for _, _, e in nodes)
    (ROOT / "scratch").mkdir(exist_ok=True)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT / "scratch", delete=False) as fh:
        fh.write(src)
        tmp = fh.name
    try:
        result = subprocess.run(["lake", "env", "lean", tmp], cwd=ROOT,
            capture_output=True, text=True, timeout=3600,
            env={**os.environ, "PATH": os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"]})
        audit(result, [e for _, _, e in nodes])
    finally:
        os.unlink(tmp)
    if "--emit" in sys.argv:
        updated = [re.sub(r"state: (?!PROVED\b)\w+", "state: SEALED", b) for b in blocks[1:]]
        (ROOT / "ledger/manifest.yaml").write_text(blocks[0] + "".join("  - id: " + b for b in updated))
    print(f"check_axioms: OK ({len(nodes)} exports; only propext, Classical.choice, Quot.sound)")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        sys.exit(f"check_axioms: FAIL: {error}")
