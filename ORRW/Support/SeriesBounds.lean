/-
Elementary series bounds used to sum the pointwise estimates of `lem:green`
over `0 ≤ r < R`.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

/-- Telescoping step behind `sum_inv_sqrt_le`: since `√(n+1) - √n = 1/(√(n+1) + √n)`,
one has `(n+1)^{-1/2} ≤ 2√(n+1) - 2√n`. -/
private lemma inv_sqrt_step (n : ℕ) :
    (1 : ℝ) / Real.sqrt ((n : ℝ) + 1)
      ≤ 2 * Real.sqrt ((n : ℝ) + 1) - 2 * Real.sqrt (n : ℝ) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  set s := Real.sqrt (n : ℝ) with hs_def
  set t := Real.sqrt ((n : ℝ) + 1) with ht_def
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
  have ht2 : t ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have ht0 : 0 < t := by
    rw [ht_def]; exact Real.sqrt_pos.mpr (by linarith)
  rw [div_le_iff₀ ht0]
  nlinarith [sq_nonneg (t - s)]

/-- `∑_{r<R} (r+1)^{-1/2} ≤ 2√R` (`orrw.tex`). -/
lemma sum_inv_sqrt_le (R : ℕ) :
    ∑ r ∈ Finset.range R, (1 : ℝ) / Real.sqrt ((r : ℝ) + 1) ≤ 2 * Real.sqrt (R : ℝ) := by
  induction R with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have h := inv_sqrt_step n
    linarith

/-- The rpow exponent `-3/2` written multiplicatively. -/
private lemma rpow_three_halves_eq {x : ℝ} (hx : 0 < x) :
    x ^ (-(3 : ℝ) / 2) = (x * Real.sqrt x)⁻¹ := by
  rw [neg_div, Real.rpow_neg hx.le, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
    Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- Telescoping step behind `sum_rpow_three_halves_le`: for `n ≥ 1`,
`(n+1)^{-3/2} ≤ 2n^{-1/2} - 2(n+1)^{-1/2}`. -/
private lemma rpow_step (n : ℕ) (hn : 1 ≤ n) :
    (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹
      ≤ 2 / Real.sqrt (n : ℝ) - 2 / Real.sqrt ((n : ℝ) + 1) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s := Real.sqrt (n : ℝ) with hs_def
  set t := Real.sqrt ((n : ℝ) + 1) with ht_def
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have ht2 : t ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.mpr hn0
  have ht0 : 0 < t := by rw [ht_def]; exact Real.sqrt_pos.mpr (by linarith)
  have hst : s ≤ t := by nlinarith [hs2, ht2, hs0, ht0]
  rw [← ht2, div_sub_div _ _ (ne_of_gt hs0) (ne_of_gt ht0), inv_eq_one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hsum : s * t ^ 2 + s ^ 2 * t ≤ 2 * t ^ 3 := by nlinarith [hst, hs0, ht0]
  have hC : (t - s) * (t + s) = 1 := by nlinarith [hs2, ht2]
  have hpos : 0 < t + s := by linarith
  have hexpand : (2 * (t - s) * t ^ 3 - s * t) * (t + s)
      = 2 * t ^ 3 * ((t - s) * (t + s)) - (s * t ^ 2 + s ^ 2 * t) := by ring
  have hmul : 0 ≤ (2 * (t - s) * t ^ 3 - s * t) * (t + s) := by
    rw [hexpand, hC]; linarith
  have hfin : (0 : ℝ) ≤ 2 * (t - s) * t ^ 3 - s * t :=
    le_of_mul_le_mul_right
      (by linarith : (0 : ℝ) * (t + s) ≤ (2 * (t - s) * t ^ 3 - s * t) * (t + s)) hpos
  linarith

/-- The telescoped form of `sum_rpow_three_halves_le`. -/
private lemma sum_rpow_aux (n : ℕ) :
    ∑ r ∈ Finset.Ico 1 (n + 1), ((r : ℝ) ^ (-(3 : ℝ) / 2)) ≤ 3 - 2 / Real.sqrt (n : ℝ) := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      norm_num [Finset.sum_Ico_succ_top]
    · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m + 1)]
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast, rpow_three_halves_eq (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
      have h := rpow_step m hm
      linarith

/-- `∑_{r=1}^{R-1} r^{-3/2} ≤ 3`, which is what makes `osc(g_R)` bounded for
`d ≥ 3`. -/
lemma sum_rpow_three_halves_le (R : ℕ) :
    ∑ r ∈ Finset.Ico 1 R, ((r : ℝ) ^ (-(3 : ℝ) / 2)) ≤ 3 := by
  cases R with
  | zero => norm_num
  | succ n =>
    have h := sum_rpow_aux n
    have h2 : (0 : ℝ) ≤ 2 / Real.sqrt (n : ℝ) := by positivity
    linarith

/-- Telescoping step behind `sum_inv_le_one_add_log`: for `n ≥ 1`,
`(n+1)^{-1} ≤ log(n+1) - log n`, since `log(n/(n+1)) ≤ n/(n+1) - 1`. -/
private lemma log_step (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1)⁻¹ ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hn0 hn1)
  rw [Real.log_div (ne_of_gt hn0) (ne_of_gt hn1)] at h
  have hkey : (n : ℝ) / ((n : ℝ) + 1) - 1 = -((n : ℝ) + 1)⁻¹ := by
    field_simp
    ring
  rw [hkey] at h
  linarith

/-- The telescoped form of `sum_inv_le_one_add_log`. -/
private lemma sum_inv_aux (n : ℕ) :
    ∑ r ∈ Finset.Ico 1 (n + 1), ((r : ℝ))⁻¹ ≤ 1 + Real.log (n : ℝ) := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      norm_num [Finset.sum_Ico_succ_top]
    · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m + 1)]
      have h := log_step m hm
      push_cast
      push_cast at ih
      linarith

/-- `∑_{r=1}^{R-1} r^{-1} ≤ 1 + log R`, which is the source of the logarithm in
the `d = 2` case of `osc(g_R)`. -/
lemma sum_inv_le_one_add_log (R : ℕ) :
    ∑ r ∈ Finset.Ico 1 R, ((r : ℝ))⁻¹ ≤ 1 + Real.log (R : ℝ) := by
  cases R with
  | zero => norm_num
  | succ n =>
    refine (sum_inv_aux n).trans ?_
    have hlog : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; norm_num
      · exact Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast Nat.le_succ n)
    linarith

end ORRW
