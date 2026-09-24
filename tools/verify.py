#!/usr/bin/env python3
"""Run the repository's build, regression tests, and verification checks."""
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
CHECKS = ("check_manifest", "check_coverage", "check_clauses", "check_constants",
          "check_exponents", "paper_anchors", "paper_citations", "sync_docs",
          "check_warnings", "check_axioms")


def main():
    env = {**os.environ, "PATH": str(Path.home() / ".elan/bin") + ":" + os.environ.get("PATH", "")}
    commands = [[sys.executable, "-m", "unittest", "discover", "-s", "tools/tests", "-v"]]
    commands += [[sys.executable, f"tools/{name}.py"] for name in CHECKS]
    commands += [[sys.executable, "tools/certificate.py", "--check"]]
    for cmd in commands:
        print("\n" + " ".join(cmd), flush=True)
        result = subprocess.run(cmd, cwd=ROOT, env=env)
        if result.returncode:
            return result.returncode
    print("\nverify: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
