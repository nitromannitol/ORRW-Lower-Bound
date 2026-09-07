"""Validate complete Lean axiom output before reporting a successful audit."""
import re

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def audit(result, exports):
    if result.returncode != 0:
        raise ValueError(f"Lean exited {result.returncode}:\n{result.stdout}\n{result.stderr}")
    found = {}
    for match in re.finditer(
        r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$",
        result.stdout, re.MULTILINE,
    ):
        name, axioms = match.groups()
        if name in found:
            raise ValueError(f"duplicate axiom output for {name}")
        found[name] = axioms or ""
    missing = set(exports) - found.keys()
    if missing:
        raise ValueError("missing axiom output: " + ", ".join(sorted(missing)))
    for name in exports:
        unexpected = {a.strip() for a in found[name].split(",") if a.strip()} - ALLOWED
        if unexpected:
            raise ValueError(f"{name}: unexpected axioms: " + ", ".join(sorted(unexpected)))
    return {name: found[name] for name in exports}
