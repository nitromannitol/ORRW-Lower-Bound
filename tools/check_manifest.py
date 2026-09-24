#!/usr/bin/env python3
"""Frozen-statement manifest checker for the ORRW formalization.

Verifies, against ledger/manifest.yaml:
  1. every manifest node's file exists and contains exactly one
     FROZEN-STATEMENT-BEGIN/END block;
  2. the sha256 of the block's bytes (marker lines excluded) matches the
     manifest;
  3. the block contains exactly one `theorem`, `def`, `abbrev`, or `structure`
     declaration and its parsed name exactly matches the manifest export;
  4. every .lean file under ORRW/Frozen/ is owned by exactly one node;
  5. `sorry` occurs in the production tree (ORRW/, ORRW.lean) only inside the
     files of theorem nodes in state DRAFT_SORRY, exactly once per such file,
     and only after the block's end marker;
  6. no `axiom`, `admit`, or `sorryAx` token occurs anywhere in the
     production tree;
  7. states are from the allowed set; definitions are never DRAFT_SORRY;
     PROVED/FROZEN files contain no sorry;
  8. when a node has `closure_sha256`, its source-level ORRW dependency-closure
     hash matches.  Nodes without the optional field are skipped and counted.

`--emit` inserts or refreshes `closure_sha256` for every node after all other
checks pass.

Closure hashes use a deliberately dependency-light, source-only heuristic; no
Lean elaborator is invoked.  The checker indexes top-level, explicitly named
`def`, `abbrev`, `structure`, `class`, `inductive`, and `opaque` commands in
`ORRW/**/*.lean` outside `ORRW/Frozen/`.  It scans comment- and string-masked
declaration text for ASCII Lean-style identifiers, resolves fully qualified
names exactly, then resolves relative names by lexical namespace, same-file
name, or a unique global suffix.  Ambiguous suffixes are skipped rather than
guessed.  A node's direct references are transitively closed through the
indexed declarations; the UTF-8 declaration bytes are concatenated in sorted
constant-key order and SHA-256 hashed.

A declaration byte span starts at its column-zero command line and ends before
the next recognized column-zero declaration or top-level command.  Frozen
declarations are not indexed a second time: their own `frozen_sha256` and
manifest node protect those bytes, while this closure covers the unfrozen ORRW
support surface that D-015 targets.

This is conservative but not an elaboration-equivalent dependency oracle.
False positives can arise when a local binder shadows a uniquely named ORRW
constant; they only make the hash cover extra bytes.  False negatives can
arise from Unicode or escaped identifiers, generated structure projections,
private-name mangling across files, notation/macro expansion, coercions,
aliases introduced by `open`/`export`, `mutual` commands, or ambiguous
unqualified suffixes.  Unusual indentation or unrecognized top-level commands
can also make the heuristic declaration span incomplete.  Imported non-ORRW
declarations are intentionally out of scope.  The hash is an integrity
tripwire, not a substitute for semantic Lean auditing.

Exit code 0 iff all checks pass.  No network, no Lake.  Dependencies are the
Python standard library and PyYAML only.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from dataclasses import dataclass
from pathlib import Path

try:
    import yaml
except ImportError:
    sys.exit("check_manifest.py: PyYAML is required (pip install pyyaml)")

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"
BEGIN = "-- FROZEN-STATEMENT-BEGIN"
END = "-- FROZEN-STATEMENT-END"
THEOREM_STATES = {"DRAFT_SORRY", "SEALED", "PROVED", "CONDITIONAL"}
DEF_STATES = {"FROZEN"}

WORD = r"(?<![A-Za-z0-9_'])"
DROW = r"(?![A-Za-z0-9_'])"
SORRY_RE = re.compile(WORD + r"sorry" + DROW)
BANNED_RE = re.compile(WORD + r"(axiom|admit|sorryAx)" + DROW)
COMMENT_LINE_RE = re.compile(r"^\s*--")
IDENT = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
FROZEN_DECL_RE = re.compile(
    rf"(?m)^[ \t]*(?:noncomputable[ \t]+)?"
    rf"(theorem|def|abbrev|structure)[ \t]+({IDENT}){DROW}")
SOURCE_DECL_RE = re.compile(
    rf"^(?P<mods>(?:(?:private|protected|noncomputable|unsafe)\s+)*)"
    rf"(?P<kind>def|abbrev|structure|class|inductive|opaque)\s+"
    rf"(?P<name>{IDENT}){DROW}")
ANY_DECL_RE = re.compile(
    rf"^(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    rf"(?:def|abbrev|structure|class|inductive|opaque|theorem|lemma|example|instance)\b")
TOP_COMMAND_RE = re.compile(
    r"^(?:/--|/-!|--|namespace\b|(?:noncomputable\s+)?section\b|end\b|open\b|"
    r"variable\b|attribute\b|include\b|omit\b|set_option\b|#)")
NAMESPACE_RE = re.compile(r"^(?:private\s+)?namespace\s+(" + IDENT + r")")
SECTION_RE = re.compile(r"^(?:noncomputable\s+)?section(?:\s+" + IDENT + r")?\s*$")
END_RE = re.compile(r"^end(?:\s+" + IDENT + r")?\s*$")
TOKEN_RE = re.compile(IDENT)
NODE_LINE_RE = re.compile(r"^  - id:\s*(\S+)\s*$")


def path_is_relative_to(path: Path, parent: Path) -> bool:
    """Python 3.8-compatible equivalent of Path.is_relative_to."""
    try:
        path.relative_to(parent)
    except ValueError:
        return False
    return True


def strip_block_comments(text: str) -> str:
    """Mask nested block comments, line comments, and strings, preserving lines."""
    out: list[str] = []
    i = 0
    depth = 0
    in_line = False
    in_string = False
    escaped = False
    while i < len(text):
        if in_line:
            if text[i] == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
        elif depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif in_string:
            ch = text[i]
            out.append("\n" if ch == "\n" else " ")
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                in_string = False
            i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif text.startswith("--", i):
            in_line = True
            out.extend("  ")
            i += 2
        elif text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


@dataclass(frozen=True)
class SourceDecl:
    """One explicitly named source declaration outside ORRW/Frozen/."""

    key: str
    full_name: str
    raw_name: str
    namespace: str
    path: Path
    start_line: int
    source_bytes: bytes


def current_namespace(scopes: list[tuple[str, str]]) -> str:
    """Return the heuristic lexical namespace represented by the scope stack."""
    parts: list[str] = []
    for kind, name in scopes:
        if kind != "namespace":
            continue
        if name.startswith("ORRW.") or name == "ORRW":
            parts = name.split(".")
        else:
            parts.extend(name.split("."))
    return ".".join(parts)


def source_declarations() -> list[SourceDecl]:
    """Index explicit ORRW declarations outside the frozen tree."""
    declarations: list[SourceDecl] = []
    orrw_root = ROOT / "ORRW"
    frozen_root = orrw_root / "Frozen"
    for path in sorted(orrw_root.rglob("*.lean")):
        if path_is_relative_to(path, frozen_root):
            continue
        text = path.read_text()
        lines = text.splitlines(keepends=True)
        offsets: list[int] = []
        offset = 0
        for line in lines:
            offsets.append(offset)
            offset += len(line)
        boundaries = []
        for line_no, line in enumerate(lines):
            if ANY_DECL_RE.match(line) or TOP_COMMAND_RE.match(line):
                boundaries.append(offsets[line_no])

        scopes: list[tuple[str, str]] = []
        for line_no, line in enumerate(lines):
            decl_match = SOURCE_DECL_RE.match(line)
            if decl_match:
                raw_name = decl_match.group("name")
                namespace = current_namespace(scopes)
                if raw_name.startswith("ORRW.") or raw_name == "ORRW":
                    full_name = raw_name
                elif namespace:
                    full_name = f"{namespace}.{raw_name}"
                else:
                    full_name = raw_name
                if not full_name.startswith("ORRW."):
                    continue
                start = offsets[line_no]
                end = next((b for b in boundaries if b > start), len(text))
                decl_text = text[start:end]
                is_private = "private" in decl_match.group("mods").split()
                rel = path.relative_to(ROOT).as_posix()
                key = full_name
                if is_private:
                    key = f"{full_name}@{rel}:{line_no + 1}"
                declarations.append(SourceDecl(
                    key=key,
                    full_name=full_name,
                    raw_name=raw_name,
                    namespace=namespace,
                    path=path,
                    start_line=line_no + 1,
                    source_bytes=decl_text.encode(),
                ))
                continue

            namespace_match = NAMESPACE_RE.match(line)
            if namespace_match:
                scopes.append(("namespace", namespace_match.group(1)))
            elif SECTION_RE.match(line):
                scopes.append(("section", ""))
            elif END_RE.match(line) and scopes:
                scopes.pop()
    return declarations


class DeclarationResolver:
    """Resolve scanned identifiers to the explicit source declaration index."""

    def __init__(self, declarations: list[SourceDecl]):
        self.declarations = declarations
        self.by_full: dict[str, list[SourceDecl]] = {}
        for decl in declarations:
            self.by_full.setdefault(decl.full_name, []).append(decl)

    @staticmethod
    def _unique(candidates: list[SourceDecl]) -> SourceDecl | None:
        unique = {candidate.key: candidate for candidate in candidates}
        return next(iter(unique.values())) if len(unique) == 1 else None

    def _resolve_exact_or_suffix(self, name: str) -> SourceDecl | None:
        exact = self._unique(self.by_full.get(name, []))
        if exact is not None:
            return exact
        suffix = f".{name}"
        return self._unique([
            decl for decl in self.declarations
            if decl.full_name == name or decl.full_name.endswith(suffix)
        ])

    def resolve(self, token: str, context: SourceDecl | None) -> SourceDecl | None:
        """Resolve the longest useful prefix of one scanned dotted token."""
        parts = token.split(".")
        prefixes = [".".join(parts[:n]) for n in range(len(parts), 0, -1)]
        for name in prefixes:
            if name.startswith("ORRW."):
                exact = self._unique(self.by_full.get(name, []))
                if exact is not None:
                    return exact
                continue
            if context is not None:
                namespace = context.namespace
                while namespace:
                    exact = self._unique(self.by_full.get(f"{namespace}.{name}", []))
                    if exact is not None:
                        return exact
                    namespace = namespace.rpartition(".")[0]
                same_file = self._unique([
                    decl for decl in self.declarations
                    if decl.path == context.path and
                    (decl.raw_name == name or decl.full_name.endswith(f".{name}"))
                ])
                if same_file is not None:
                    return same_file
            resolved = self._resolve_exact_or_suffix(name)
            if resolved is not None:
                return resolved
        return None

    def closure(self, source: str) -> set[SourceDecl]:
        """Return the transitive explicit ORRW declaration closure of source."""
        closure: dict[str, SourceDecl] = {}
        frontier: list[SourceDecl] = []
        masked = strip_block_comments(source)
        for token in TOKEN_RE.findall(masked):
            resolved = self.resolve(token, None)
            if resolved is not None and resolved.key not in closure:
                closure[resolved.key] = resolved
                frontier.append(resolved)
        while frontier:
            current = frontier.pop()
            body = strip_block_comments(current.source_bytes.decode())
            for token in TOKEN_RE.findall(body):
                resolved = self.resolve(token, current)
                if resolved is not None and resolved.key not in closure:
                    closure[resolved.key] = resolved
                    frontier.append(resolved)
        return set(closure.values())


def closure_digest(source: str, resolver: DeclarationResolver) -> tuple[str, int]:
    """Hash name-sorted declaration bytes in the transitive source closure."""
    closure = resolver.closure(source)
    payload = b"".join(decl.source_bytes for decl in sorted(closure, key=lambda d: d.key))
    return hashlib.sha256(payload).hexdigest(), len(closure)


def frozen_declaration(block: str, path: Path, errors: list[str]) -> tuple[str, str] | None:
    """Parse the unique supported declaration keyword and exact name in a block."""
    matches = FROZEN_DECL_RE.findall(strip_block_comments(block))
    if len(matches) != 1:
        errors.append(
            f"{path}: expected exactly one theorem/def/abbrev/structure "
            f"declaration in frozen block, found {len(matches)}")
        return None
    return matches[0]


def emit_closure_hashes(manifest_text: str, hashes: dict[str, str]) -> str:
    """Insert or replace closure_sha256 fields without reformatting YAML."""
    lines = manifest_text.splitlines(keepends=True)
    starts = [(i, match.group(1)) for i, line in enumerate(lines)
              if (match := NODE_LINE_RE.match(line))]
    for position in range(len(starts) - 1, -1, -1):
        start, node_id = starts[position]
        end = starts[position + 1][0] if position + 1 < len(starts) else len(lines)
        if node_id not in hashes:
            raise ValueError(f"no computed closure hash for manifest node {node_id}")
        closure_line = f"    closure_sha256: {hashes[node_id]}\n"
        existing = next((i for i in range(start, end)
                         if lines[i].startswith("    closure_sha256:")), None)
        if existing is not None:
            lines[existing] = closure_line
            continue
        frozen = next((i for i in range(start, end)
                       if lines[i].startswith("    frozen_sha256:")), None)
        if frozen is None:
            raise ValueError(f"manifest node {node_id} has no frozen_sha256 line")
        lines.insert(frozen + 1, closure_line)
    return "".join(lines)


def block_of(text: str, path: Path, errors: list) -> tuple[str, int] | None:
    """Return (block_bytes, end_offset) for the unique frozen block."""
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        errors.append(f"{path}: expected exactly one {BEGIN}/{END} pair")
        return None
    b = text.index(BEGIN) + len(BEGIN)
    e = text.index(END)
    if e < b:
        errors.append(f"{path}: END marker precedes BEGIN marker")
        return None
    block = text[b:e]
    if block.startswith("\n"):
        block = block[1:]
    return block, e + len(END)


def check_source_pin(manifest: dict) -> None:
    """Require the manuscript bytes named by the manifest's source pin."""
    pin = manifest.get("source_pin")
    if not isinstance(pin, dict) or not pin.get("file") or not pin.get("sha256"):
        raise ValueError("missing manuscript source pin")
    path = ROOT / pin["file"]
    if not path.is_file():
        raise ValueError(f"missing pinned manuscript: {pin['file']}")
    if hashlib.sha256(path.read_bytes()).hexdigest() != pin["sha256"]:
        raise ValueError(f"manuscript source hash mismatch: {pin['file']}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--emit", action="store_true",
        help="insert or refresh closure_sha256 for every manifest node")
    args = parser.parse_args()

    errors: list[str] = []
    manifest_text = MANIFEST.read_text()
    manifest = yaml.safe_load(manifest_text)
    try:
        check_source_pin(manifest)
    except ValueError as error:
        print(f"check_manifest: FAIL: {error}")
        return 1
    nodes = manifest.get("nodes") or []
    declarations = source_declarations()
    resolver = DeclarationResolver(declarations)
    closure_hashes: dict[str, str] = {}
    closure_checked = 0
    closure_skipped = 0

    owned: dict[Path, dict] = {}
    for node in nodes:
        nid = node.get("id", "<missing id>")
        path = ROOT / node["file"]
        kind = node.get("kind")
        state = node.get("state")
        if kind == "theorem" and state not in THEOREM_STATES:
            errors.append(f"{nid}: theorem state {state!r} not allowed")
        if kind == "definition" and state not in DEF_STATES:
            errors.append(f"{nid}: definition state {state!r} not allowed")
        if kind not in ("theorem", "definition"):
            errors.append(f"{nid}: unknown kind {kind!r}")
        if path in owned:
            errors.append(f"{path}: owned by both {owned[path]['id']} and {nid}")
        owned[path] = node
        if not path.exists():
            errors.append(f"{nid}: file {path} does not exist")
            continue
        text = path.read_text()
        got = block_of(text, path, errors)
        if got is None:
            continue
        block, end_off = got
        digest = hashlib.sha256(block.encode()).hexdigest()
        if digest != node.get("frozen_sha256"):
            errors.append(
                f"{nid}: frozen bytes hash {digest[:16]}… does not match "
                f"manifest {str(node.get('frozen_sha256'))[:16]}…")
        parsed = frozen_declaration(block, path, errors)
        if parsed is not None:
            declaration_kind, declaration_name = parsed
            export = node.get("export", "")
            if declaration_name != export:
                errors.append(
                    f"{nid}: frozen declaration name {declaration_name!r} does not "
                    f"exactly match export {export!r}")
            if kind == "theorem" and declaration_kind != "theorem":
                errors.append(
                    f"{nid}: manifest kind theorem but frozen declaration uses "
                    f"{declaration_kind}")
            if kind == "definition" and declaration_kind not in {
                    "def", "abbrev", "structure"}:
                errors.append(
                    f"{nid}: manifest kind definition but frozen declaration uses "
                    f"{declaration_kind}")
        closure_hash, closure_size = closure_digest(block, resolver)
        closure_hashes[nid] = closure_hash
        expected_closure = node.get("closure_sha256")
        if expected_closure is None:
            closure_skipped += 1
        else:
            closure_checked += 1
            if not args.emit and closure_hash != expected_closure:
                errors.append(
                    f"{nid}: closure hash {closure_hash[:16]}… does not match "
                    f"manifest {str(expected_closure)[:16]}… "
                    f"({closure_size} declarations)")
        code = strip_block_comments(text)
        n_sorry = len(SORRY_RE.findall(code))
        if state == "DRAFT_SORRY":
            if n_sorry != 1:
                errors.append(f"{nid}: state {state} requires exactly one "
                              f"sorry in {path}, found {n_sorry}")
            elif SORRY_RE.search(strip_block_comments(text[:end_off])):
                errors.append(f"{nid}: sorry occurs before the end marker")
        elif state == "CONDITIONAL":
            if n_sorry:
                errors.append(f"{nid}: CONDITIONAL but {path} contains its own sorry")
        elif n_sorry:
            errors.append(f"{nid}: state {state} but {path} contains sorry")

    frozen_dir = ROOT / "ORRW" / "Frozen"
    if frozen_dir.exists():
        for f in sorted(frozen_dir.rglob("*.lean")):
            if f not in owned:
                errors.append(f"{f}: frozen file has no manifest owner")

    draft_files = {ROOT / n["file"] for n in nodes
                   if n.get("state") == "DRAFT_SORRY"}
    prod = [ROOT / "ORRW.lean"] + sorted((ROOT / "ORRW").rglob("*.lean"))
    for f in prod:
        if not f.exists():
            continue
        code = strip_block_comments(f.read_text())
        if BANNED_RE.search(code):
            tok = BANNED_RE.search(code).group(1)
            errors.append(f"{f}: banned token `{tok}` in production tree")
        if f not in draft_files and SORRY_RE.search(code):
            errors.append(f"{f}: unregistered sorry")

    if errors:
        print("check_manifest: FAIL")
        for e in errors:
            print(f"  - {e}")
        return 1
    if args.emit:
        if len(closure_hashes) != len(nodes):
            print("check_manifest: FAIL")
            print("  - cannot emit: not every node produced a closure hash")
            return 1
        MANIFEST.write_text(emit_closure_hashes(manifest_text, closure_hashes))
        print(
            f"check_manifest: emitted closure_sha256 for {len(nodes)} nodes "
            f"from {len(declarations)} indexed ORRW declarations")
        return 0
    n_draft = sum(1 for n in nodes if n.get("state") == "DRAFT_SORRY")
    print(
        f"check_manifest: OK ({len(nodes)} nodes, {n_draft} unsealed; "
        f"closure {closure_checked} checked, {closure_skipped} skipped; "
        f"{len(declarations)} ORRW declarations indexed)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
