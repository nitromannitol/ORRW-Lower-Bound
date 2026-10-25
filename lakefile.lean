import Lake

open Lake DSL

package «orrw_formalization» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "d6dc1aaae0ad1bdfd353cb7e1817a41406131e18"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

/-- The comparator audit surface (`ORRWAudit/*/Challenge.lean`, `ORRWAudit/*/SolutionBasic.lean`,
`ORRWAudit/*/Solution.lean` and `ORRWAudit/Support/`).  Not a default target: it builds only on
demand (`lake build ORRWAudit`), so the ordinary build of `ORRW` is unchanged. -/
lean_lib «ORRWAudit» where
  globs := #[.submodules `ORRWAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

@[default_target]
lean_lib «ORRW» where
  globs := #[.andSubmodules `ORRW]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]
