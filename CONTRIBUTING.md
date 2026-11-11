# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues and
pull requests are welcome.

## Building locally

```bash
lake exe cache get   # first time: prebuilt mathlib
lake build           # compile the project
```

The toolchain is pinned in `lean-toolchain`. The production build is required to emit no Lean
or linter warnings (`python3 tools/check_warnings.py`). The four mathlib-only files
`ORRWAudit/*/Challenge.lean` are the only files with a `sorry`: each contains one documented
statement-level `sorry`, checked against its completed solution by `leanprover/comparator`.
`lake build ORRW` builds the library and `lake build ORRWAudit` the comparator libraries.

## The main results and the axiom audit

The main results `ORRW.range_lower_bound`, `ORRW.range_tail`, `ORRW.range_ae` and
`ORRW.occupation_measure` are in `ORRW/MainTheorems.lean`. To print their axiom reports and
those of all registered statements:

```bash
lake build ORRW.Meta.AxiomsAudit      # the four main theorems
lake env lean ORRW/Certificate.lean   # all 24 registered statements
python3 tools/verify.py               # every checker
```

`ORRW/Meta/AxiomsAudit.lean` is not imported by the library root, because a `#print axioms`
command runs again whenever its module is rebuilt. Each report must list exactly `propext`,
`Classical.choice` and `Quot.sound`; `tools/check_axioms.py` fails on `sorryAx` and on any
other axiom. The checkers in `tools/` need Python 3.10 or newer and PyYAML
(`python3 -m pip install -r tools/requirements.txt`).

## Conventions for Lean files

- No `sorry`, `admit` or new `axiom` in the library; `python3 tools/check_manifest.py` rejects
  them.
- **Frozen statements.** The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `ORRW/Frozen/` is pinned by the SHA-256 recorded in
  `ledger/manifest.yaml`. A change there shows up in `python3 tools/check_manifest.py` and must
  be recorded in the manifest; proofs after the end marker may be changed freely. Statements
  refer to the paper by LaTeX label.
- **Library lemmas.** Lattice objects that do not depend on the reinforced walk (the Dirichlet
  Laplacian, exit times, effective resistance, the resistance packing bound, the insertion
  inequality, the lazy walk and its Green function, and the elementary geometry of direction
  words) come from the shared library Lattice-Probability; new model-independent lemmas belong
  there. The dependencies under `.lake/packages/` are read-only.
- **Never run `lake clean`.** It wipes the mathlib oleans and forces a multi-hour rebuild from
  source. To force a project-only rebuild, remove the project build artifacts under
  `.lake/build/lib/lean/ORRW` (and the corresponding `.lake/build/ir/ORRW`) and re-run
  `lake build`.
- **Per-file rebuilds.** Lake invalidates by content hash, not modification time, so `touch`
  does nothing; delete the specific `.olean` under `.lake/build/lib/lean/` and rebuild the
  module.

### Elaboration policy for new files

These rules keep new files cheap to elaborate; apply them to any file you add.

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with
  `nlinarith`. When a nonlinear fact is needed, hoist it into a small `private`
  lemma over abstract real variables, so that `Real.rpow` and `Real.exp` terms
  never enter a numeric tactic. In particular, do not call `nlinarith` on a
  goal that mentions `rpow` or `exp`.
- Before `ring` or `field_simp` on an expression built with `set`, run
  `clear_value` on the bound names; otherwise the let-bodies are unfolded inside
  the tactic.
- Do not split a file, narrow its imports, or add an instance cache "for
  performance" without a warm profile before and after
  (`lake env lean --profile <file>`). The profiler's default 100 ms floor hides
  diffuse costs; use `-D profiler.threshold=1` when hunting them.
- Keep Lean files under 1500 lines.

## Comparators

Each pair under `ORRWAudit/<Pair>/` has a `Challenge.lean` that imports mathlib only, a
`Solution.lean`, a `SolutionBasic.lean` and a `comparator.json` that permits exactly `propext`,
`Classical.choice` and `Quot.sound`. Do not add a declaration to a challenge that the statement
does not need, and do not change a challenge without checking it against the paper's statement.
`ORRWAudit/check_standalone.sh` elaborates one file standalone with the project's options. The
command that runs a pair is in [`ORRWAudit/README.md`](ORRWAudit/README.md) and
[`ORRWAudit/COMPARATOR_RUNS.md`](ORRWAudit/COMPARATOR_RUNS.md). A missing pair, a missing tool
or a failed kernel check is a failure.

## Continuous integration

- `build.yml` (**CI**) builds the library, rejects any warning or `sorry` warning, builds the
  axiom audit module, and runs `tools/verify.py`.
- `comparator.yml` (**Comparator audit**) builds `ORRWAudit` and runs the comparator on all four
  pairs.

Both run on pushes to `main` that change Lean files, `tools/`, `paper/`, `ledger/`,
`formalization.yaml` or the build configuration, and can be started manually.
