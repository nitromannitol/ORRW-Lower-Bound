/-
Frozen statement of Lemma 3.1 of Bou-Rabee--Peres, *Once-reinforced random walk
on `ℤ^d` has range exponent at least `d/(d+1)`*, Section 3, Lemma
(A supermartingale), label `lem:martingale`, `orrw.tex:596-599`:

  "Let `d ≥ 1` and `β ≥ 1`.  Then `(n + Φ_n - Γ_n)_{n≥0}` is a supermartingale
   for the filtration `(F_n)_{n≥0}`."

What is frozen is the paper's own drift inequality, `orrw.tex`
(`eq:drift`), which the proof states is "the assertion":

  "`E_β[Γ_{n+1} - Γ_n - (Φ_{n+1} - Φ_n) | F_n] ≥ 1`."

Modelling decisions.

* Ruling F-501 (no `MeasureTheory.Supermartingale`).  Under ruling R-001 the law
  of the first `n` steps is a probability mass function on the finite set
  `Fin n → Dir d`; there is no measure on infinite paths and no filtration in
  Mathlib's sense, so Mathlib's `Supermartingale` is deliberately not used.  The
  faithful reading of `lem:martingale` under R-001 is `eq:drift`, which is what
  the paper itself proves and calls "the assertion".

* Ruling F-502 (conditioning on `F_n` is conditioning on a prefix).  A history
  of length `m` is a word `v : Fin m → Dir d`, and the conditional law of the
  next step given that history is the step rule of `ORRW/Basic.lean`: direction
  `a` has conditional probability `stepWeight β v m a / totalWeight β v m`.  The
  conditional expectation of `eq:drift` is therefore the explicit weighted
  `Finset` sum over `a : Dir d` below, divided by the normalizer, which is the
  paper's `μ_n` (`ORRW.mu`, equal to `ORRW.totalWeight` by
  `ORRW.mu_eq_totalWeight`, ruling P-006).  The division is not by zero:
  `ORRW.totalWeight_pos` gives `μ > 0` for `d ≥ 1` and `β ≥ 1`.

* Ruling F-503 (both times are read along the extended word).  `Φ_m`, `Γ_m`,
  `Φ_{m+1}` and `Γ_{m+1}` are all evaluated at the word `Fin.snoc v a` of length
  `m + 1`, so that the increments are increments of one process.  The time-`m`
  terms do not in fact depend on `a`: by `ORRW.pos_init` and `ORRW.E_init` every
  quantity at a time `k ≤ m` is unchanged by dropping the last letter, so
  `Φ (Fin.snoc v a) m = Φ v m` and likewise for `Γ`.

* Ruling F-504 (hypotheses).  `d ≥ 1` and `β ≥ 1` are the paper's own
  hypotheses.  Neither forces the conclusion: the inequality is an assertion
  about the potential and the charge, both of which are defined through the
  Dirichlet-Laplacian objects of `ORRW/Lattice.lean`.
-/
import ORRW.Potential
import ORRW.Support.Drift

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.supermartingale_drift {d : ℕ} (hd : 1 ≤ d) {β : ℝ} (hβ : 1 ≤ β)
    (m : ℕ) (v : Fin m → Dir d) :
    1 ≤ (∑ a : Dir d, stepWeight β v m a *
            ((Gamma β (Fin.snoc v a) (m + 1) - Gamma β (Fin.snoc v a) m)
              - (Phi (Fin.snoc v a) (m + 1) - Phi (Fin.snoc v a) m)))
          / mu β v m
-- FROZEN-STATEMENT-END
:= ORRW.Support.drift_ge_one hd hβ m v
