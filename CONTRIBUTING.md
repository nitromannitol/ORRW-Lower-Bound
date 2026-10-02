# Contributing / Building notes

This repository is primarily a finished artifact rather than an actively
solicited collaborative project, but issues and pull requests are welcome.

## Building locally

```bash
lake exe cache get   # first time: prebuilt Mathlib
lake build           # compile the project
```

The production build is required to emit no Lean or linter warnings
(`python3 tools/check_warnings.py`).  The four Mathlib-only files
`Audit/*/Challenge.lean` are the sole exception: each contains one documented
statement-level `sorry`, checked against its completed solution by
`leanprover/comparator`.

A few practical notes for working with this development:

- **Never run `lake clean`.**  It wipes the Mathlib oleans and forces a
  multi-hour rebuild from source.  To force a project-only rebuild, remove the
  project build artifacts under `.lake/build/lib/lean/ORRW` (and the
  corresponding `.lake/build/ir/ORRW`) and re-run `lake build`.

- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so
  `touch` does nothing; delete the specific `.olean` under
  `.lake/build/lib/lean/` and rebuild the module.

- **Frozen statements.**  The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `ORRW/Frozen/` is pinned by the SHA-256
  recorded in `ledger/manifest.yaml`.  A change there shows up in
  `python3 tools/check_manifest.py` and must be recorded in the manifest;
  proofs after the end marker may be changed freely.

- **Library lemmas.**  Lattice objects that do not depend on the reinforced
  walk (the Dirichlet Laplacian, exit times, effective resistance, the
  resistance packing bound, the insertion inequality, the lazy walk and its
  Green function, and the elementary geometry of direction words) come from
  the shared library Lattice-Probability; new model-independent lemmas belong
  there.

- **The main results** are in `ORRW/MainTheorems.lean`; the axiom audit is
  `lake build ORRW.Meta.AxiomsAudit`, and the comparator surface is
  `lake build Audit`.  `python3 tools/verify.py` runs every checker.

## Elaboration policy for new files

These rules keep new files cheap to elaborate; apply them to any file you add.

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with
  `nlinarith`.  When a nonlinear fact is needed, hoist it into a small `private`
  lemma over abstract real variables, so that `Real.rpow` and `Real.exp` terms
  never enter a numeric tactic.  In particular, do not call `nlinarith` on a
  goal that mentions `rpow` or `exp`.
- Before `ring` or `field_simp` on an expression built with `set`, run
  `clear_value` on the bound names; otherwise the let-bodies are unfolded inside
  the tactic.
- Do not split a file, narrow its imports, or add an instance cache "for
  performance" without a warm profile before and after
  (`lake env lean --profile <file>`).  The profiler's default 100 ms floor hides
  diffuse costs; use `-D profiler.threshold=1` when hunting them.
- Keep Lean files under 1500 lines.
- Never run `lake clean`; see the building notes above.
