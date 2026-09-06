/-
Frozen statement of the corollary recorded inside Theorem 8.2 of
Bou-Rabee--Peres, *Once-reinforced random walk on `ℤ^d` has range exponent at
least `d/(d+1)`*, Section 8, Theorem (Occupation of a site), label `thm:return`,
display `eq:cesaro` (`orrw.tex:1227-1247`):

  "and dividing by `n`,
     `sup_{z ∈ ℤ^d} (1/n) ∑_{j=0}^{n-1} P_β{X_j = z} ≤ C β n^{-d/(d+1)}`
   `(n ≥ 1)`."

It is `eq:occupation` at `m = 0` and `h = n`, after the simplification
`(β-1)^{d/(d+1)} ≤ β` and `log(h+2) ≤ C h^{1/(d+1)}`, divided by `n`.  The
supremum over sites is rendered as a universal quantifier inside the scope of
the single constant `C` (ruling R-006), which is what makes it the paper's
`sup_z` and not the weaker `∀ z, ∃ C`.

Modelling decisions.

* Ruling F-821 (probabilities at one horizon).  As in ruling F-811, each
  `P_β{X_j = 0}` is `ORRW.prb M β (fun w => ORRW.pos w j = 0)` at a single
  horizon `M`, and `M` is quantified over every horizon with `N ≤ M`.  The
  Cesaro window `N` and the horizon `M` are different quantities and are given
  different names; at `M = N` the statement is the paper's display literally.

* Ruling F-822 (`N ≥ 1` is the paper's hypothesis and is load bearing).  The
  display carries `(N ≥ 1)`.  Without it the instance `N = 0` would be the empty
  sum times `1 / 0 = 0` bounded by `C β · Real.rpow 0 (-d/(d+1)) = 0`, which is
  true but says nothing; the hypothesis removes that content-free instance.

* Ruling F-823 (`C` is bound before `β`, `N` and `M`).  The constant is the `C`
  of `thm:return`, which depends only on `d`.

* Ruling F-824 (real exponents).  `N^{-d/(d+1)}` is a `Real.rpow` power with the
  exponent formed in `ℝ`.

* Ruling F-825 (`1/N` is written as a factor).  The display is
  `(1/N) ∑ … ≤ …`; the left-hand side is kept in that form rather than cleared,
  so that the statement is the paper's, not an equivalent rearrangement.

Vacuity.  The bound is a genuine decay claim: the left-hand side is an average
of probabilities, so it is at most `1`, while the right-hand side tends to `0`.
It cannot hold for the wrong reason by the left-hand side vanishing: the term
`j = 0` is `ORRW.prb M β (fun w => ORRW.pos w 0 = 0)`, whose event is all of the
sample space, so it equals `1` by `ORRW.Frozen.sum_prob_eq_one` and the sum is
always at least `1`.  The claim therefore forces `C β N^{1/(d+1)} ≥ 1`, which is
consistent, and rules out `C = 0`.  Non-degenerate instance: `d = 2`, `β = 3`,
`N = 5`, `M = 5`, where the right-hand side is `3C · 5^{-2/3} ≈ 1.03 C` and the
left-hand side lies in `[1/5, 1]`.
-/
import ORRW.Basic
import ORRW.Support.Occupation
import ORRW.Frozen.Occupation.Occupation

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.occupation_cesaro (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β → ∀ N : ℕ, 1 ≤ N → ∀ M : ℕ, N ≤ M → ∀ z : ORRW.Site d,
      (1 / (N : ℝ)) * ∑ j ∈ Finset.range N,
          ORRW.prb (d := d) M β (fun w => ORRW.pos w j = z)
        ≤ C * β * (N : ℝ) ^ (-(d : ℝ) / ((d : ℝ) + 1))
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨C, hC⟩ := ORRW.Frozen.occupation d hd
  refine ⟨7 * max C 0, fun β hβ N hN M hM z => ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmain := hC β hβ z 0 N hN M (by omega)
  have hrange : Finset.Ico 0 (0 + N) = Finset.range N := by
    rw [zero_add, Finset.range_eq_Ico]
  rw [hrange] at hmain
  have hPnn : (0 : ℝ) ≤ (N : ℝ) ^ (1 / ((d : ℝ) + 1)) :=
    Real.rpow_nonneg (le_of_lt hNpos) _
  have hHnn : (0 : ℝ) ≤ (if d = 2 then Real.log ((N : ℝ) + 2) else 1) := by
    by_cases h2 : d = 2
    · rw [if_pos h2]
      exact Real.log_nonneg (by linarith)
    · rw [if_neg h2]; norm_num
  have hSnn : (0 : ℝ) ≤ (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) * (N : ℝ) ^ (1 / ((d : ℝ) + 1)) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) hPnn
  have hH := ORRW.H_le_rpow d hd hN
  have hS : (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) * (N : ℝ) ^ (1 / ((d : ℝ) + 1))
      ≤ β * (N : ℝ) ^ (1 / ((d : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (ORRW.rpow_sub_one_le d hβ) hPnn
  have hCle : C * ((if d = 2 then Real.log ((N : ℝ) + 2) else 1)
        + (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) * (N : ℝ) ^ (1 / ((d : ℝ) + 1)))
      ≤ max C 0 * ((if d = 2 then Real.log ((N : ℝ) + 2) else 1)
        + (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) * (N : ℝ) ^ (1 / ((d : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  have hM0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hbound : ∑ j ∈ Finset.range N, ORRW.prb (d := d) M β (fun w => ORRW.pos w j = z)
      ≤ max C 0 * (7 * β * (N : ℝ) ^ (1 / ((d : ℝ) + 1))) := by
    refine le_trans hmain (le_trans hCle ?_)
    refine mul_le_mul_of_nonneg_left ?_ hM0
    have hβ7 : (6 : ℝ) + β ≤ 7 * β := by linarith
    nlinarith [hH, hS, hPnn]
  have hkey : (N : ℝ) ^ (1 / ((d : ℝ) + 1)) / (N : ℝ)
      = (N : ℝ) ^ (-(d : ℝ) / ((d : ℝ) + 1)) := by
    have hne : ((d : ℝ) + 1) ≠ 0 := by positivity
    rw [show (-(d : ℝ) / ((d : ℝ) + 1)) = 1 / ((d : ℝ) + 1) - 1 from by field_simp; ring,
      Real.rpow_sub hNpos, Real.rpow_one]
  have hinv : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  calc (1 / (N : ℝ)) * ∑ j ∈ Finset.range N,
        ORRW.prb (d := d) M β (fun w => ORRW.pos w j = z)
      ≤ (1 / (N : ℝ)) * (max C 0 * (7 * β * (N : ℝ) ^ (1 / ((d : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left hbound (le_of_lt hinv)
    _ = 7 * max C 0 * β * ((N : ℝ) ^ (1 / ((d : ℝ) + 1)) / (N : ℝ)) := by ring
    _ = 7 * max C 0 * β * (N : ℝ) ^ (-(d : ℝ) / ((d : ℝ) + 1)) := by rw [hkey]
