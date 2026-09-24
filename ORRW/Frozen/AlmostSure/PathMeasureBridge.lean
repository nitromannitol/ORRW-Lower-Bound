/-
Frozen statement of the bridge between the infinite-path measure and the
finite-word law.

This is not a statement of the paper.  It is the one thing that has to be true
for the paper's two almost-sure corollaries to be expressible at all: ruling
R-001 measures each time separately, and an almost-sure statement needs one
measure covering every time at once.  `ORRW.pathMeasure` is that measure, built
from the one-step kernels by the Ionescu-Tulcea theorem in
`ORRW/Support/InfinitePath.lean`; this says its finite-dimensional marginals are
the `ORRW.prob` of `orrw.tex` (label `thm:main`, the model of `ssec:main-results`).

Modelling decisions.

* Ruling A-001 (the restriction is Mathlib's).  `ORRW.restr n` is definitionally
  `Preorder.frestrictLe n`, proved by `ORRW.restr_eq_frestrictLe`, so the
  cylinder below is the cylinder Mathlib's `traj_map_frestrictLe` computes.

* Ruling A-002 (`Fact` hypotheses).  `0 < d` and `1 ≤ β` are carried as `Fact`
  instances because `Kernel.traj` demands the Markov property by instance
  resolution, and that property needs both.

Proof.  `ORRW.pathMeasure_restr_eq_bind` reduces the cylinder to an
`initTraj`-average of `Kernel.partialTraj` -- the only use of Ionescu-Tulcea --
and `ORRW.bind_partialTraj_eval` evaluates that average by induction on `n`,
matching `ORRW.prob_succ` step for step.
-/
import ORRW.Support.InfinitePath

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.pathMeasure_restr {d : ℕ} [Fact (0 < d)] {β : ℝ} [Fact (1 ≤ β)]
    (n : ℕ) (x : Π _i : Finset.Iic n, ORRW.Dir d) :
    ORRW.pathMeasure (d := d) β {ω | ORRW.restr n ω = x}
      = ENNReal.ofReal (ORRW.prob β (ORRW.ofPrefix n x))
-- FROZEN-STATEMENT-END
:= by
  rw [ORRW.pathMeasure_restr_eq_bind (β := β) n x, ORRW.bind_partialTraj_eval (β := β) n x]
