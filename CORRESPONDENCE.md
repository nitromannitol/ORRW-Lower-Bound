# Correspondence: paper ↔ Lean

Maps every frozen declaration to *Once-reinforced random walk on `ℤ^d` has
range exponent at least `d/(d+1)`* (Bou-Rabee–Peres).

The [paper result map](README.md#which-lean-theorem-proves-which-result) gives
printed result numbers, descriptions, stable labels, links to both statements,
and notes on differences in formulation.

## Conventions

- The paper is pinned at `paper/orrw.tex`; its SHA-256 is in
  `ledger/manifest.yaml`.  Source locations are `orrw.tex:<line range>` plus
  the LaTeX `\label` name. Keep labels as the stable identifiers; the reader
  map adds printed numbers generated from the manuscript.
- The bytes between `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END`
  are the contract.  A proof attempt may only fill in what follows the end
  marker.  `frozen_sha256` in the manifest pins those bytes.  The recipe is
  exact and worth stating, because a reader who guesses it wrongly concludes
  the pins are broken: take the file's text, start just past the BEGIN marker,
  stop just before the END marker, drop one leading newline if it is there, and
  take the SHA-256 of the UTF-8 encoding of what remains.  Neither marker line
  is included.  `python3 tools/check_manifest.py` is the authority.
- `state` is `SEALED` once the statement is frozen, a proof exists, and the
  proof's axiom closure has been checked to contain no `sorryAx`.  Every node
  in this development is `SEALED`; `tools/check_axioms.py` verifies it.

## Modelling rulings

| id | ruling |
|---|---|
| R-001 | The law of the first `n` steps is a probability mass function on the finite set of direction words `Fin n → Dir d`, not a measure on infinite paths.  Every quantity the two main theorems mention is a function of the first `n` steps, so no infinite-horizon measure and no measurability side condition arises.  `ssec:main-results`. |
| R-002 | A site of `ℤ^d` is `Fin d → ℤ` and a step is a `Dir d = Fin d × Bool`; the walk is recorded by its direction word, so the sample space is a `Fintype` and expectations are `Finset` sums. |
| R-003 | `prb` takes a `Prop`-valued predicate and sums `prob w * ite (P w) 1 0` under `Classical`, so that no decidability instance can quietly change which event is being measured. |

### Where a Lean statement is not literally the paper's

The following entries describe the principal modelling conventions.
[VERIFICATION.md](VERIFICATION.md) records the changes in constant notation
and the revised occupation corollary in the current manuscript snapshot.

| paper | how the Lean statement differs | why |
|---|---|---|
| `lem:exp` | both statements use the ORRW filtration and give bounds at every finite horizon; Lean represents `Φ_{n∧ζ}`, `Γ_{n∧ζ}` and `n∧ζ` as functions of finite histories and assumes the stopped one-step drift | the author approved specializing the paper on 2026-09-05.  The frozen Lean statement and its constants are unchanged.  Every printed stopping time satisfies the increment identities required in Lean; see F-601 through F-605 |
| `lem:schur` | the identification `Reff(x ↔ (A⁺)^c) = -Δ_{A⁺}^{-1}(x,x)` is a definition, not a proved statement | ruling L-002.  The other five assertions of the lemma, including both identities of `eq:hbound`, are proved |
| `lem:martingale` | the paper says `(n + Φ_n - Γ_n)` is a supermartingale; the Lean statement is the equivalent one-step drift `1 ≤ E[ΔΓ - ΔΦ]` | that drift is the paper's own `eq:drift`, and it is what the proof of `prop:tail` consumes |

The occupation estimates have separate declarations for the interval bound,
the introductory occupation bound, and the older time-averaged corollary.
The last is weaker in its dependence on reinforcement than the current
`eq:cesaro`; see VERIFICATION.md. Proposition `prop:displacement` has separate
finite-horizon and almost-sure declarations.

### The infinite-path law

R-001 models the law of the first `n` steps as a pmf on `Fin n -> Dir d`, so it
has no measure on infinite paths of its own.  Two claims in the paper are about
all times at once and so could not be stated under it:

| paper | claim | node |
|---|---|---|
| after `thm:whp` | `liminf |R_n| n^{-d/(d+1)} >= c b^{-d/(d+1)}` a.s. | `ae-range` |
| closing display of `prop:displacement` | `liminf Λ_n n^{-1/(d+1)} >= c b^{-1/(d+1)}` a.s. | `ae-displacement` |

Both are now formalized.  `ORRW/Support/InfinitePath.lean` builds
`ORRW.pathMeasure`, the law of the walk on infinite direction words, from the
one-step kernels by the Ionescu-Tulcea theorem; `bridge-path-measure` proves its
finite-dimensional marginals are exactly `ORRW.prob`; and
`ORRW.pathMeasure_event` transfers any fixed-time event across that identity.
The two claims then follow by Borel-Cantelli, as the paper says they do.

`prop:charge` says "almost surely" and is formalized directly, because it is
rendered for every direction word, which is strictly stronger than for almost
every one.  `tools/check_coverage.py` confirms that every theorem, lemma and
proposition in the paper is claimed by a node.

### Where each ruling is written down

`R-001`-`R-003` are above.  The rest live beside the definitions they govern, so
that a reader meets the ruling and the object together.  This index exists so
that a cross-reference such as "see ruling L-002" can actually be followed.

| ruling | subject | written in |
|---|---|---|
| `L-001` | `u` is the linear-algebra formula, not a probabilistic expectation | `ORRW/Lattice.lean` |
| `L-002` | `Reff` is *defined* by the Schur identity, so the electrical content of `eq:schur` is not formalized | `ORRW/Lattice.lean` |
| `L-003` | functions on `A` are extended by zero via `extendZero` | `ORRW/Lattice.lean` |
| `L-004` | `Matrix.inv` is junk on a singular matrix; `dirichletLaplacian_isUnit` rules that out | `ORRW/Lattice.lean` |
| `R-006` | a `sup` over sites is rendered as a `∀` inside the constant's scope | `ORRW/Frozen/Occupation/OccupationMeasure.lean` |
| `F-***`, `W-***` | per-node transcription decisions | the header of the frozen file that uses them |

`R-004` and `R-005` are retired: they governed an earlier Section 8 argument
that no longer appears here, and nothing in `ORRW/` depends on them.

## Frozen surface

<!-- FROZEN-SURFACE-BEGIN (generated by tools/sync_docs.py) -->

| id | Lean | paper | state |
|---|---|---|---|
| `thm-main` | [ORRW.Frozen.range_lower_bound](ORRW/Frozen/RangeLowerBound.lean#L18) | [thm:main](paper/orrw.tex#L112) | SEALED |
| `thm-whp` | [ORRW.Frozen.range_tail](ORRW/Frozen/RangeTail.lean#L20) | [thm:whp](paper/orrw.tex#L128) | SEALED |
| `lem-max-exit` | [ORRW.Frozen.max_exit](ORRW/Frozen/Insertion/ExitTimeBounds.lean#L34) | [lem:max-exit](paper/orrw.tex#L423) | SEALED |
| `lem-schur` | [ORRW.Frozen.one_point_insertion](ORRW/Frozen/Insertion/OnePointInsertion.lean#L38) | [lem:schur](paper/orrw.tex#L447) | SEALED |
| `lem-packing` | [ORRW.Frozen.resistance_packing](ORRW/Frozen/Insertion/ResistancePacking.lean#L34) | [lem:packing](paper/orrw.tex#L485) | SEALED |
| `lem-insertion` | [ORRW.Frozen.insertion_inequality](ORRW/Frozen/Insertion/InsertionInequality.lean#L34) | [lem:insertion](paper/orrw.tex#L515) | SEALED |
| `guard-total-weight-pos` | [ORRW.Frozen.totalWeight_pos](ORRW/Frozen/Guards/TotalWeightPos.lean#L14) | model guard for ORRW.stepProb (ORRW/Basic.lean) | SEALED |
| `guard-prob-pmf` | [ORRW.Frozen.sum_prob_eq_one](ORRW/Frozen/Guards/ProbIsPMF.lean#L15) | model guard for ORRW.prob (ORRW/Basic.lean) | SEALED |
| `guard-edges-le-sites` | [ORRW.Frozen.card_edges_le_card_range](ORRW/Frozen/Guards/EdgesLeSites.lean#L18) | [eq:edges-sites](paper/orrw.tex#L723) | SEALED |
| `guard-one-step-witness` | [ORRW.Frozen.expect_card_range_one_step](ORRW/Frozen/Guards/OneStepWitness.lean#L20) | numeric witness for the normalization of ORRW.expect | SEALED |
| `lem-martingale` | [ORRW.Frozen.supermartingale_drift](ORRW/Frozen/Potential/Supermartingale.lean#L51) | [lem:martingale](paper/orrw.tex#L596) | SEALED |
| `lem-walk-order` | [ORRW.Frozen.insertion_order](ORRW/Frozen/Potential/InsertionOrder.lean#L58) | [lem:walk-order](paper/orrw.tex#L632) | SEALED |
| `prop-charge` | [ORRW.Frozen.accumulated_charge](ORRW/Frozen/Potential/AccumulatedCharge.lean#L42) | [prop:charge](paper/orrw.tex#L669) | SEALED |
| `lem-exp` | [ORRW.Frozen.time_versus_charge](ORRW/Frozen/Tail/TimeVersusCharge.lean#L73) | [lem:exp](paper/orrw.tex#L739) | SEALED |
| `prop-tail` | [ORRW.Frozen.sigma_tail](ORRW/Frozen/Tail/SigmaTail.lean#L43) | [prop:tail](paper/orrw.tex#L792) | SEALED |
| `prop-displacement` | [ORRW.Frozen.displacement](ORRW/Frozen/Tail/Displacement.lean#L63) | [prop:displacement](paper/orrw.tex#L863) | SEALED |
| `prop-beta-sharp` | [ORRW.Frozen.exponents_optimal](ORRW/Frozen/Tail/ExponentsOptimal.lean#L43) | [prop:beta-sharp](paper/orrw.tex#L912) | SEALED |
| `lem-green` | [ORRW.Frozen.lazy_green_bounds](ORRW/Frozen/Occupation/LazyGreen.lean#L92) | [lem:green](paper/orrw.tex#L991) | SEALED |
| `thm-occupation` | [ORRW.Frozen.occupation](ORRW/Frozen/Occupation/Occupation.lean#L70) | [thm:return](paper/orrw.tex#L1039) | SEALED |
| `thm-occupation-cesaro` | [ORRW.Frozen.occupation_cesaro](ORRW/Frozen/Occupation/OccupationCesaro.lean#L20) | [eq:cesaro](paper/orrw.tex#L1102) | SEALED |
| `thm-occupation-measure` | [ORRW.Frozen.occupation_measure](ORRW/Frozen/Occupation/OccupationMeasure.lean#L26) | [thm:occupation-intro](paper/orrw.tex#L145) | SEALED |
| `bridge-path-measure` | [ORRW.Frozen.pathMeasure_restr](ORRW/Frozen/AlmostSure/PathMeasureBridge.lean#L34) | not a paper statement; required for the almost-sure corollaries (see CORRESPONDENCE.md, R-001 scope) | SEALED |
| `ae-range` | [ORRW.Frozen.range_ae](ORRW/Frozen/AlmostSure/RangeAlmostSure.lean#L35) | [paper passage](paper/orrw.tex#L138), the Borel-Cantelli corollary stated in prose after thm:whp (ruling A-003) | SEALED |
| `ae-displacement` | [ORRW.Frozen.displacement_ae](ORRW/Frozen/AlmostSure/DisplacementAlmostSure.lean#L29) | [prop:displacement](paper/orrw.tex#L863), almost-sure clause | SEALED |

<!-- FROZEN-SURFACE-END -->

## Why the guards are frozen anchors

The following statements check that the definitions have the intended
normalization and nondegeneracy:

1. `stepProb` divides by `totalWeight`.  Division by zero is `0` in Lean, so a
   vanishing denominator would make `prob ≡ 0` and every expectation bound in
   the development true and worthless.  `guard-total-weight-pos` excludes it,
   and `guard-prob-pmf` is its positive form.
2. `Matrix.inv` is the junk value `0` on a singular matrix, so a mean-exit-time
   defined through it would be identically zero unless the Dirichlet Laplacian
   is proved invertible.
3. `h_A x` is only meaningful for `x ∉ A`; a statement quantified without that
   hypothesis can be true for the wrong reason.

`guard-one-step-witness` pins the normalization against a value computable by
hand: with `d = 2`, one step, the expected range is exactly `2`.
