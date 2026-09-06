/-
Frozen statement of Lemma 8.1 of Bou-Rabee--Peres, *Once-reinforced random walk
on `ℤ^d` has range exponent at least `d/(d+1)`*, Section 8, Lemma (Truncated
Green function), label `lem:green`, `orrw.tex:1179-1195`:

  "Let `d ≥ 2` and let `R ≥ 1` be an integer.  Then
     `‖Q^R(0,·)‖_∞ ≤ C R^{-d/2}`,
     `osc(g_R) ≤ C log(R+1)` for `d = 2` and `osc(g_R) ≤ C` for `d ≥ 3`,
     `∑_{{x,y}} |g_R(y) - g_R(x)| ≤ 4 d^{3/2} √R`,
   the last sum running over the undirected edges of `ℤ^d`."

The two objects the lemma is about are fixed at `orrw.tex`, whose
display carries the label `eq:gR` (`orrw.tex`):

  "Let `P` be the transition operator of simple random walk on `ℤ^d`, let
   `Q := ½(I + P)` be its lazy version, and for an integer `R ≥ 1` put
     `g_R := ∑_{r=0}^{R-1} Q^r(0,·)`,
     `osc(g_R) := max g_R - min g_R`."

They are built in `ORRW/LazyWalk.lean` as `ORRW.Q`, `ORRW.delta0` and
`ORRW.gR`, with ruling W-001 identifying `Q^[r] delta0` with `Q^r(0,·)`.

Modelling decisions.

* Ruling F-801 (`C` is bound before `R`).  The lemma inherits `C` from the
  surrounding prose, where it is a constant depending only on `d`.  It is
  therefore bound existentially outside the quantifier on `R`, after `d`, so
  that one constant serves every `R`.  A `C` bound after `R` would be a much
  weaker and essentially empty assertion.

* Ruling F-802 (`R ≥ 1` is load bearing).  At `R = 0` the first bound is false
  as stated rather than vacuous: `g_0 = 0` and `Q^[0] delta0 0 = 1`, while
  `Real.rpow 0 (-d/2) = 0`.  The paper's own hypothesis `R ≥ 1` is kept.

* Ruling F-803 (the sup norm is stated pointwise).  `Q^R(0,·)` is nonnegative
  (`ORRW.iterate_delta0_nonneg`), so `‖Q^R(0,·)‖_∞ ≤ B` is exactly
  `∀ x, Q^R(0,x) ≤ B`.  The pointwise form is used, so that no supremum over an
  infinite index set has to be shown to exist and no `sSup` junk value can make
  the bound hold for the wrong reason.

* Ruling F-804 (the oscillation is stated pairwise).  `max g_R - min g_R` is a
  difference of two extrema over the infinite lattice.  `osc(g_R) ≤ B` is
  rendered as `∀ x y, g_R x - g_R y ≤ B`, which is the same assertion and needs
  neither attainment nor a junk `iSup`.  Quantifying `x` and `y` independently
  also gives the absolute-value form, by swapping them.

* Ruling F-805 (the undirected edges are parametrized by a site and a
  coordinate).  Each undirected edge of `ℤ^d` is `{x, x + e_i}` for exactly one
  pair `(x, i)`, namely the endpoint `x` with the smaller `i`-th coordinate
  together with that coordinate.  The sum is therefore taken over
  `Site d × Fin d`, which counts each edge exactly once, and not over
  `Sym2 (Site d)`.  This is the same parametrization as `ORRW.edgeOf`, which
  `ORRW/Support/Guards.lean` already uses for `eq:edges-sites`; the alternative,
  a sum over `Sym2 (Site d)` restricted to adjacent pairs, would need a
  well-definedness argument for the summand on an unordered pair and would carry
  the same content.  That the count is exactly one per edge is proved, not
  argued: `ORRW.edgeParam_injective` and `ORRW.edgeParam_surjective`.  It
  matters, because the third bound carries an explicit constant: a
  parametrization that named each edge twice would double the left-hand side.

* Ruling F-806 (summability is asserted, not assumed).  The point of the
  truncation is that the total variation over *all* edges of `ℤ^d` is finite, so
  finiteness is part of the claim and `Summable` is a conjunct.  Without it the
  bound would be satisfied by the junk value `∑' = 0` of a non-summable family.
  It is true: `g_R` is supported in the box of radius `R`
  (`ORRW.iterate_delta0_eq_zero`), so only finitely many terms are nonzero.

* Ruling F-807 (real exponents).  `R^{-d/2}`, `d^{3/2}` and `√R` are `Real.rpow`
  powers and `Real.sqrt`; the exponents are formed in `ℝ`, not by truncated
  subtraction or division in `ℕ`.

* Ruling F-808 (the two cases are merged).  `if d = 2 then Real.log (R+1) else 1`
  reproduces the paper's display in both of its cases, since the hypothesis
  `2 ≤ d` makes the two cases exhaustive.

Vacuity.  None of the three bounds is trivially true.  `Q^R(0,·)` is a
probability distribution (`ORRW.Q_iterate_one`), so the first bound is a genuine
decay claim and not merely `≤ 1`.  For the second, `g_R ≥ 0` with
`g_R(0) ≥ 1` (`ORRW.one_le_gR_zero`) and `g_R` vanishing off a finite box, so the
left-hand side is at least `1` for suitable `x, y` and the bound forces
`C log(R+1) ≥ 1` at `d = 2` and `C ≥ 1` at `d ≥ 3`: it cannot be met by taking
`C = 0`.  The third has no free constant at all.  At `d = 2`, `R = 4` the three
right-hand sides are `C/4`, `C log 5` and `4·2^{3/2}·2 ≈ 22.6`, all finite and
positive.
-/
import ORRW.LazyWalk
import ORRW.Support.LazyGreenBounds

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.lazy_green_bounds (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, ∀ R : ℕ, 1 ≤ R →
      (∀ x : ORRW.Site d, ORRW.Q^[R] (ORRW.delta0 : ORRW.Site d → ℝ) x
          ≤ C * (R : ℝ) ^ (-(d : ℝ) / 2))
      ∧ (∀ x y : ORRW.Site d, ORRW.gR R x - ORRW.gR R y
          ≤ C * (if d = 2 then Real.log ((R : ℝ) + 1) else 1))
      ∧ Summable (fun p : ORRW.Site d × Fin d =>
          |ORRW.gR R (p.1 + ORRW.dirVec (p.2, true)) - ORRW.gR R p.1|)
      ∧ (∑' p : ORRW.Site d × Fin d,
            |ORRW.gR R (p.1 + ORRW.dirVec (p.2, true)) - ORRW.gR R p.1|)
          ≤ 4 * (d : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (R : ℝ)
-- FROZEN-STATEMENT-END
:= by
  have hd0 : 0 < d := by omega
  refine ⟨2 + 3 * ORRW.greenConst d, fun R hR => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro x
    have hnn : (0 : ℝ) ≤ (R : ℝ) ^ (-(d : ℝ) / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg R) _
    have hle : ORRW.greenConst d ≤ 2 + 3 * ORRW.greenConst d := by
      have := ORRW.greenConst_nonneg d
      linarith
    exact le_trans (ORRW.iterate_delta0_sup_bound hd0 hR x)
      (mul_le_mul_of_nonneg_right hle hnn)
  · intro x y
    exact ORRW.gR_osc_bound hd hR x y
  · exact ORRW.summable_gR_gradient R
  · exact ORRW.gR_tv_bound hd0 R
