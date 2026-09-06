/-
The three estimates of `lem:green` (`orrw.tex`).

The sup bound is proved without Fourier analysis: the schedule decomposition of
`ORRW/Support/LazyDecomp.lean` bounds `Q^r(0,x)` by the schedule average of
`∏_i (N_i+1)^{-1/2}`, and a Chernoff estimate for the multinomial counts
(`ORRW/Support/LazyMoment.lean`) shows that average is `O(r^{-d/2})`.  The
oscillation bound is that estimate summed over `0 ≤ r < R`.  The total variation
bound is the paper's own argument, with the constant `4 d^{3/2} √R` unchanged.
-/
import Mathlib
import ORRW.Support.LazyBox
import ORRW.Support.LazyMoment
import ORRW.Support.SeriesBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

variable {d : ℕ}

/-! ### The schedule average of `∏_i (N_i+1)^{-1/2}` -/

/-- Bound on the reciprocal of a coordinate count used in the multinomial Chernoff estimate behind the sup bound. -/
lemma one_div_sqrt_cnt_le_one {r : ℕ} (c : Fin r → Fin d) (i : Fin d) :
    (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) ≤ 1 := by
  have hge : (1 : ℝ) ≤ (cnt c i : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (cnt c i : ℝ) := Nat.cast_nonneg _
    linarith
  have h1 : (1 : ℝ) ≤ Real.sqrt ((cnt c i : ℝ) + 1) :=
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt hge
  rw [div_le_one (by linarith)]
  exact h1

/-- Confirms the multinomial count factor in the schedule product is a positive weight, as needed for the sup and oscillation bounds on the Green kernel. -/
lemma one_div_sqrt_cnt_nonneg {r : ℕ} (c : Fin r → Fin d) (i : Fin d) :
    (0 : ℝ) ≤ (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) := by positivity

/-- Either some coordinate is updated at most `a` times, or every factor of the
product is at most `(a+2)^{-1/2}`. -/
lemma sched_prod_bound {r : ℕ} (c : Fin r → Fin d) (a : ℕ) :
    ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
      ≤ ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d
        + ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0) := by
  by_cases hex : ∃ i : Fin d, cnt c i ≤ a
  · obtain ⟨i₀, hi₀⟩ := hex
    have hone : (1 : ℝ) ≤ ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0) := by
      calc (1 : ℝ) = (if cnt c i₀ ≤ a then (1 : ℝ) else 0) := by rw [if_pos hi₀]
        _ ≤ _ := Finset.single_le_sum (f := fun i => (if cnt c i ≤ a then (1 : ℝ) else 0))
              (fun i _ => by dsimp only; split <;> norm_num) (Finset.mem_univ i₀)
    have hprod : ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) ≤ 1 := by
      calc ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
          ≤ ∏ _i : Fin d, (1 : ℝ) :=
            Finset.prod_le_prod (fun i _ => one_div_sqrt_cnt_nonneg c i)
              (fun i _ => one_div_sqrt_cnt_le_one c i)
        _ = 1 := by simp
    have : (0 : ℝ) ≤ ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d := by positivity
    linarith
  · push_neg at hex
    have hfac : ∀ i : Fin d,
        (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) ≤ (Real.sqrt ((a : ℝ) + 2))⁻¹ := by
      intro i
      have ha : (a : ℝ) + 2 ≤ (cnt c i : ℝ) + 1 := by
        have : a + 1 ≤ cnt c i := hex i
        have : ((a : ℝ) + 1) ≤ (cnt c i : ℝ) := by exact_mod_cast this
        linarith
      have hpos : (0 : ℝ) < Real.sqrt ((a : ℝ) + 2) := Real.sqrt_pos.mpr (by positivity)
      rw [one_div, inv_le_inv₀ (by positivity) hpos]
      exact Real.sqrt_le_sqrt ha
    have hsum : (0 : ℝ) ≤ ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun i _ => by split <;> norm_num
    have hprod : ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
        ≤ ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d := by
      calc ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
          ≤ ∏ _i : Fin d, (Real.sqrt ((a : ℝ) + 2))⁻¹ :=
            Finset.prod_le_prod (fun i _ => one_div_sqrt_cnt_nonneg c i) (fun i _ => hfac i)
        _ = ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d := by simp
    linarith

/-! ### Real-power conversions

The frozen statement uses `Real.rpow`; the proofs below work with `Real.sqrt`
and natural powers, and these two lemmas are the only bridge needed. -/

/-- Technical rewrite lemma identifying a power of a natural number with the corresponding real exponentiation, used to state the three green-estimate bounds in the form the paper uses. -/
lemma rpow_neg_half_eq (d R : ℕ) :
    (R : ℝ) ^ (-(d : ℝ) / 2) = ((Real.sqrt (R : ℝ)) ^ d)⁻¹ := by
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
  have h1 : (Real.sqrt (R : ℝ)) ^ d = (R : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((R : ℝ) ^ ((1 : ℝ) / 2)) d,
      ← Real.rpow_mul hR0]
    congr 1
    ring
  rw [h1, ← Real.rpow_neg hR0]
  congr 1
  ring

/-- Rewrites d^{3/2} as d times its square root, the form in which the total variation constant 4 d^{3/2} √R is stated. -/
lemma rpow_three_halves (d : ℕ) : (d : ℝ) ^ ((3 : ℝ) / 2) = (d : ℝ) * Real.sqrt (d : ℝ) := by
  have h0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by ring,
    Real.rpow_add_of_nonneg h0 (by norm_num) (by norm_num), Real.rpow_one]

/-! ### The constant -/

/-- The constant of `lem:green`, explicit. -/
noncomputable def greenConst (d : ℕ) : ℝ :=
  (Real.sqrt (4 * (d : ℝ))) ^ d + (d : ℝ) * (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d

/-- Confirms the Green constant is nonnegative, as needed when it appears as a lower bound on the walk's range weight. -/
lemma greenConst_nonneg (d : ℕ) : 0 ≤ greenConst d := by
  unfold greenConst
  have h1 : (0 : ℝ) ≤ (Real.sqrt (4 * (d : ℝ))) ^ d := by positivity
  have h2 : (0 : ℝ) ≤ (d : ℝ) * (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d := by positivity
  linarith

/-! ### The sup bound -/

/-- Bounds the number of schedules of a given length, the combinatorial input needed to normalize the schedule average in the sup estimate. -/
lemma card_sched (r : ℕ) :
    ((Finset.univ : Finset (Fin r → Fin d)).card : ℝ) = (d : ℝ) ^ r := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  push_cast
  ring

/-- The Chernoff step: the schedule average of `∏_i (N_i+1)^{-1/2}` splits into a
bulk term and `d` tail terms. -/
lemma sched_sum_bound (hd : 0 < d) (R : ℕ) :
    ∑ c : Fin R → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
      ≤ (d : ℝ) ^ R * ((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ d
        + (d : ℝ) * ((d : ℝ) ^ R * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) := by
  classical
  set a : ℕ := R / (4 * d) with ha
  have step1 : ∑ c : Fin R → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
      ≤ ∑ c : Fin R → Fin d, (((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d
          + ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0)) :=
    Finset.sum_le_sum fun c _ => sched_prod_bound c a
  have step2 : ∑ c : Fin R → Fin d, (((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d
        + ∑ i : Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0))
      = (d : ℝ) ^ R * ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d
        + ∑ i : Fin d, ∑ c : Fin R → Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, card_sched, Finset.sum_comm]
  have step3 : ∑ i : Fin d, ∑ c : Fin R → Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0)
      ≤ (d : ℝ) * ((d : ℝ) ^ R * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) := by
    calc ∑ i : Fin d, ∑ c : Fin R → Fin d, (if cnt c i ≤ a then (1 : ℝ) else 0)
        ≤ ∑ _i : Fin d, ((d : ℝ) ^ R * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) :=
          Finset.sum_le_sum fun i _ => sum_indicator_cnt_le hd R i
      _ = (d : ℝ) * ((d : ℝ) ^ R * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith [step1, step2.le, step3]

/-- The bulk term. -/
lemma bulk_le (hd : 0 < d) {R : ℕ} (hR : 1 ≤ R) :
    ((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ d
      ≤ (Real.sqrt (4 * (d : ℝ))) ^ d * ((Real.sqrt (R : ℝ)) ^ d)⁻¹ := by
  have hmod : R < 4 * d * (R / (4 * d) + 1) := by
    have h2 : 0 < 4 * d := by omega
    calc R = 4 * d * (R / (4 * d)) + R % (4 * d) := (Nat.div_add_mod R (4 * d)).symm
      _ < 4 * d * (R / (4 * d)) + 4 * d := by have := Nat.mod_lt R h2; omega
      _ = 4 * d * (R / (4 * d) + 1) := by ring
  set a : ℕ := R / (4 * d) with ha
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hRle : (R : ℝ) / (4 * (d : ℝ)) ≤ (a : ℝ) + 2 := by
    have : (R : ℝ) ≤ 4 * (d : ℝ) * ((a : ℝ) + 2) := by
      have : (R : ℝ) < 4 * (d : ℝ) * ((a : ℝ) + 1) := by exact_mod_cast hmod
      nlinarith [hdR]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hsq : Real.sqrt ((R : ℝ) / (4 * (d : ℝ))) ≤ Real.sqrt ((a : ℝ) + 2) :=
    Real.sqrt_le_sqrt hRle
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hsqpos : (0 : ℝ) < Real.sqrt ((R : ℝ) / (4 * (d : ℝ))) :=
    Real.sqrt_pos.mpr (by positivity)
  have hinv : (Real.sqrt ((a : ℝ) + 2))⁻¹
      ≤ Real.sqrt (4 * (d : ℝ)) / Real.sqrt (R : ℝ) := by
    have := inv_le_inv₀ (lt_of_lt_of_le hsqpos hsq) hsqpos |>.mpr hsq
    rw [Real.sqrt_div (le_of_lt hRpos)] at this
    rwa [inv_div] at this
  have hnn : (0 : ℝ) ≤ (Real.sqrt ((a : ℝ) + 2))⁻¹ := by positivity
  calc ((Real.sqrt ((a : ℝ) + 2))⁻¹) ^ d
      ≤ (Real.sqrt (4 * (d : ℝ)) / Real.sqrt (R : ℝ)) ^ d := pow_le_pow_left₀ hnn hinv d
    _ = (Real.sqrt (4 * (d : ℝ))) ^ d * ((Real.sqrt (R : ℝ)) ^ d)⁻¹ := by
        rw [div_pow, div_eq_mul_inv]

/-- The tail term. -/
lemma tail_le (hd : 0 < d) {R : ℕ} (hR : 1 ≤ R) :
    (d : ℝ) * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))
      ≤ (d : ℝ) * (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d * ((Real.sqrt (R : ℝ)) ^ d)⁻¹ := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  set s : ℝ := (R : ℝ) / (4 * (d : ℝ)) with hs
  have hspos : (0 : ℝ) < s := by rw [hs]; positivity
  have hterm : s ^ d / (Nat.factorial d : ℝ) ≤ Real.exp s := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (le_of_lt hspos) (d + 1))
    refine Finset.single_le_sum (f := fun i => s ^ i / (Nat.factorial i : ℝ)) ?_ ?_
    · intro i _
      positivity
    · simp
  have hpos : (0 : ℝ) < s ^ d / (Nat.factorial d : ℝ) := by positivity
  have hexp : Real.exp (-s) ≤ (Nat.factorial d : ℝ) / s ^ d := by
    rw [Real.exp_neg]
    have h := (inv_le_inv₀ (lt_of_lt_of_le hpos hterm) hpos).mpr hterm
    rwa [inv_div] at h
  have hsd : s ^ d = (R : ℝ) ^ d / (4 * (d : ℝ)) ^ d := by rw [hs, div_pow]
  have hfac : (Nat.factorial d : ℝ) / s ^ d
      = (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d / (R : ℝ) ^ d := by
    rw [hsd]
    field_simp
  have hsr : Real.sqrt (R : ℝ) ≤ (R : ℝ) := by
    have h1 : (R : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith
    calc Real.sqrt (R : ℝ) ≤ Real.sqrt ((R : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
      _ = (R : ℝ) := Real.sqrt_sq (le_of_lt hRpos)
  have hge : (Real.sqrt (R : ℝ)) ^ d ≤ (R : ℝ) ^ d :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsr d
  have hinvle : ((R : ℝ) ^ d)⁻¹ ≤ ((Real.sqrt (R : ℝ)) ^ d)⁻¹ := by
    have h1 : (0 : ℝ) < (Real.sqrt (R : ℝ)) ^ d := by
      have : (0 : ℝ) < Real.sqrt (R : ℝ) := Real.sqrt_pos.mpr hRpos
      positivity
    exact inv_le_inv₀ (lt_of_lt_of_le h1 hge) h1 |>.mpr hge
  have hpos : (0 : ℝ) ≤ (d : ℝ) * (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d := by positivity
  rw [show -(R : ℝ) / (4 * (d : ℝ)) = -s from by rw [hs]; ring]
  calc (d : ℝ) * Real.exp (-s)
      ≤ (d : ℝ) * ((Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d / (R : ℝ) ^ d) := by
        rw [← hfac]
        exact mul_le_mul_of_nonneg_left hexp (le_of_lt hdR)
    _ = ((d : ℝ) * (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d) * ((R : ℝ) ^ d)⁻¹ := by
        field_simp
    _ ≤ ((d : ℝ) * (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d) * ((Real.sqrt (R : ℝ)) ^ d)⁻¹ :=
        mul_le_mul_of_nonneg_left hinvle hpos

/-- `‖Q^R(0,·)‖_∞ ≤ C R^{-d/2}` (`orrw.tex`). -/
theorem iterate_delta0_sup_bound (hd : 0 < d) {R : ℕ} (hR : 1 ≤ R) (x : Site d) :
    Q^[R] (delta0 : Site d → ℝ) x ≤ greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdRpow : (0 : ℝ) < (d : ℝ) ^ R := by positivity
  have h1 := iterate_delta0_le_sched hd R x
  have h2 := sched_sum_bound (d := d) hd R
  have h3 : Q^[R] (delta0 : Site d → ℝ) x
      ≤ ((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ d
        + (d : ℝ) * Real.exp (-(R : ℝ) / (4 * (d : ℝ))) := by
    refine le_trans h1 ?_
    rw [div_le_iff₀ hdRpow]
    calc ∑ c : Fin R → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
        ≤ _ := h2
      _ = (((Real.sqrt (((R / (4 * d) : ℕ) : ℝ) + 2))⁻¹) ^ d
            + (d : ℝ) * Real.exp (-(R : ℝ) / (4 * (d : ℝ)))) * (d : ℝ) ^ R := by ring
  rw [rpow_neg_half_eq d R, greenConst, add_mul]
  linarith [h3, bulk_le (d := d) hd hR, tail_le (d := d) hd hR]

/-! ### The oscillation bound -/

/-- Upper bound on the Green kernel at the origin, the first of the three estimates giving the O(r^{-d/2}) decay of the walk's potential. -/
lemma gR_le (hd : 0 < d) {R : ℕ} (hR : 1 ≤ R) (x : Site d) :
    gR R x ≤ 1 + ∑ r ∈ Finset.Ico 1 R, greenConst d * (r : ℝ) ^ (-(d : ℝ) / 2) := by
  have hsplit : Finset.range R = insert 0 (Finset.Ico 1 R) := by
    ext t
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hnot : (0 : ℕ) ∉ Finset.Ico 1 R := by simp
  have h0 : Q^[0] (delta0 : Site d → ℝ) x ≤ 1 := by
    rw [Function.iterate_zero_apply]
    unfold delta0
    split <;> norm_num
  have hrest : ∀ r ∈ Finset.Ico 1 R, Q^[r] (delta0 : Site d → ℝ) x
      ≤ greenConst d * (r : ℝ) ^ (-(d : ℝ) / 2) := by
    intro r hr
    exact iterate_delta0_sup_bound hd (Finset.mem_Ico.mp hr).1 x
  unfold gR
  rw [hsplit, Finset.sum_insert hnot]
  exact add_le_add h0 (Finset.sum_le_sum hrest)

/-- `osc(g_R) ≤ C log(R+1)` for `d = 2` and `≤ C` for `d ≥ 3` (`orrw.tex`). -/
theorem gR_osc_bound (hd : 2 ≤ d) {R : ℕ} (hR : 1 ≤ R) (x y : Site d) :
    gR R x - gR R y
      ≤ (2 + 3 * greenConst d) * (if d = 2 then Real.log ((R : ℝ) + 1) else 1) := by
  have hd0 : 0 < d := by omega
  have hg : 0 ≤ greenConst d := greenConst_nonneg d
  have hxy : gR R x - gR R y ≤ gR R x := by
    have := gR_nonneg R y
    linarith
  have hmain := gR_le hd0 hR x
  by_cases hd2 : d = 2
  · subst hd2
    rw [if_pos rfl]
    have hterm : ∀ r ∈ Finset.Ico 1 R,
        greenConst 2 * ((r : ℝ) ^ (-((2 : ℕ) : ℝ) / 2)) = greenConst 2 * ((r : ℝ))⁻¹ := by
      intro r hr
      have hr1 : 1 ≤ r := (Finset.mem_Ico.mp hr).1
      have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
      congr 1
      rw [show -((2 : ℕ) : ℝ) / 2 = -1 from by norm_num, Real.rpow_neg_one]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hmain
    have hharm := sum_inv_le_one_add_log R
    have hlogR : Real.log (R : ℝ) ≤ Real.log ((R : ℝ) + 1) := by
      refine Real.log_le_log ?_ (by linarith)
      exact_mod_cast hR
    have hlog2 : (1 : ℝ) ≤ 2 * Real.log ((R : ℝ) + 1) := by
      have h2 : (2 : ℝ) ≤ (R : ℝ) + 1 := by
        have : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
        linarith
      have := Real.log_le_log (by norm_num) h2
      have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      linarith
    have hlognn : (0 : ℝ) ≤ Real.log ((R : ℝ) + 1) := by linarith
    nlinarith [hmain, hxy, hharm, hlogR, hlog2, hg, hlognn]
  · rw [if_neg hd2]
    have hd3 : 3 ≤ d := by omega
    have hterm : ∀ r ∈ Finset.Ico 1 R,
        greenConst d * ((r : ℝ) ^ (-(d : ℝ) / 2)) ≤ greenConst d * ((r : ℝ) ^ (-(3 : ℝ) / 2)) := by
      intro r hr
      have hr1 : 1 ≤ r := (Finset.mem_Ico.mp hr).1
      have hr1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      refine mul_le_mul_of_nonneg_left ?_ hg
      refine Real.rpow_le_rpow_of_exponent_le hr1' ?_
      have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd3
      linarith
    have hsum : ∑ r ∈ Finset.Ico 1 R, greenConst d * ((r : ℝ) ^ (-(d : ℝ) / 2))
        ≤ greenConst d * 3 := by
      calc ∑ r ∈ Finset.Ico 1 R, greenConst d * ((r : ℝ) ^ (-(d : ℝ) / 2))
          ≤ ∑ r ∈ Finset.Ico 1 R, greenConst d * ((r : ℝ) ^ (-(3 : ℝ) / 2)) :=
            Finset.sum_le_sum hterm
        _ = greenConst d * ∑ r ∈ Finset.Ico 1 R, ((r : ℝ) ^ (-(3 : ℝ) / 2)) := by
            rw [Finset.mul_sum]
        _ ≤ greenConst d * 3 := mul_le_mul_of_nonneg_left (sum_rpow_three_halves_le R) hg
    linarith [hmain, hxy, hsum]

/-! ### The total variation bound -/

/-- Supplies the multinomial Chernoff estimate behind the sup bound, controlling the schedule average of the inverse square root counts by O(r^{-d/2}). -/
lemma sum_inv_sqrt_cnt_le (hd : 0 < d) (r : ℕ) (i : Fin d) :
    ∑ c : Fin r → Fin d, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)
      ≤ (d : ℝ) ^ r * (Real.sqrt (d : ℝ) / Real.sqrt ((r : ℝ) + 1)) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdpow : (0 : ℝ) < (d : ℝ) ^ r := by positivity
  set T : ℝ := ∑ c : Fin r → Fin d, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) with hT
  have hTnn : 0 ≤ T := Finset.sum_nonneg fun c _ => one_div_sqrt_cnt_nonneg c i
  have hsq : ∀ c : Fin r → Fin d,
      ((1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)) ^ 2 = (1 : ℝ) / ((cnt c i : ℝ) + 1) := by
    intro c
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin r → Fin d))
    (fun _ => (1 : ℝ)) (fun c => (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hCS
  rw [Finset.sum_congr rfl fun c _ => hsq c] at hCS
  have hcard : ((Fintype.card (Fin r → Fin d) : ℕ) : ℝ) = (d : ℝ) ^ r := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  rw [hcard] at hCS
  have hV := sum_inv_cnt_succ_le (d := d) r i
  have hrpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hT2 : T ^ 2 ≤ ((d : ℝ) ^ r * (Real.sqrt (d : ℝ) / Real.sqrt ((r : ℝ) + 1))) ^ 2 := by
    have hstep : T ^ 2 ≤ (d : ℝ) ^ r * ((d : ℝ) ^ (r + 1) / ((r : ℝ) + 1)) := by
      refine le_trans hCS ?_
      exact mul_le_mul_of_nonneg_left hV (le_of_lt hdpow)
    have hrhs : ((d : ℝ) ^ r * (Real.sqrt (d : ℝ) / Real.sqrt ((r : ℝ) + 1))) ^ 2
        = (d : ℝ) ^ r * ((d : ℝ) ^ (r + 1) / ((r : ℝ) + 1)) := by
      rw [mul_pow, div_pow, Real.sq_sqrt (le_of_lt hdR), Real.sq_sqrt (le_of_lt hrpos),
        ← pow_mul]
      rw [pow_succ]
      field_simp
      ring
    rw [hrhs]
    exact hstep
  have hrhsnn : (0 : ℝ) ≤ (d : ℝ) ^ r * (Real.sqrt (d : ℝ) / Real.sqrt ((r : ℝ) + 1)) := by
    positivity
  nlinarith [hT2, hTnn, hrhsnn]

/-- Bounds the total variation distance, over the box of sites, between the r-step walk distribution started at the origin and the same distribution started one step in the i-direction. -/
lemma sum_box_abs_diff_iterate_le (hd : 0 < d) {r L : ℕ} (hrL : r + 1 ≤ L) (i : Fin d) :
    ∑ x ∈ box d L, |Q^[r] (delta0 : Site d → ℝ) (x + dirVec ((i, true) : Dir d))
        - Q^[r] (delta0 : Site d → ℝ) x|
      ≤ 2 * (Real.sqrt (d : ℝ) / Real.sqrt ((r : ℝ) + 1)) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdpow : (0 : ℝ) < (d : ℝ) ^ r := by positivity
  refine le_trans (sum_box_abs_diff_iterate hd hrL i) ?_
  rw [div_le_iff₀ hdpow]
  calc ∑ c : Fin r → Fin d, 2 * P1 (cnt c i) 0
      ≤ ∑ c : Fin r → Fin d, 2 * ((1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)) :=
        Finset.sum_le_sum fun c _ => by
          have := P1_zero_le_inv_sqrt (cnt c i)
          linarith
    _ = 2 * ∑ c : Fin r → Fin d, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * ((d : ℝ) ^ r * (Real.sqrt (d : ℝ) / Real.sqrt ((r : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (sum_inv_sqrt_cnt_le hd r i) (by norm_num)
    _ = 2 * (Real.sqrt (d : ℝ) / Real.sqrt ((r : ℝ) + 1)) * (d : ℝ) ^ r := by ring

/-- The potential of the Green kernel is constant (with zero gradient) at sites outside the box of radius R, which is the boundary condition used in the charge and resistance estimates. -/
lemma gR_grad_eq_zero_of_notMem {R : ℕ} {p : Site d × Fin d}
    (hp : p ∉ box d (R + 1) ×ˢ (Finset.univ : Finset (Fin d))) :
    |gR R (p.1 + dirVec (p.2, true)) - gR R p.1| = 0 := by
  have hp1 : p.1 ∉ box d (R + 1) := fun h =>
    hp (Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩)
  obtain ⟨j, hj⟩ := exists_of_notMem_box hp1
  have h1 : gR R p.1 = 0 := by
    refine gR_eq_zero_of_lt (i := j) ?_
    push_cast at hj ⊢
    omega
  have h2 : gR R (p.1 + dirVec (p.2, true)) = 0 := by
    refine gR_eq_zero_of_lt (i := j) ?_
    have hb : |dirVec ((p.2, true) : Dir d) j| ≤ 1 := abs_dirVec_le_one _ j
    have hcoord : (p.1 + dirVec ((p.2, true) : Dir d)) j
        = p.1 j + dirVec ((p.2, true) : Dir d) j := rfl
    have habs : |p.1 j| ≤ |p.1 j + dirVec ((p.2, true) : Dir d) j|
        + |dirVec ((p.2, true) : Dir d) j| := by
      simpa using abs_add_le (p.1 j + dirVec ((p.2, true) : Dir d) j)
        (-(dirVec ((p.2, true) : Dir d) j))
    rw [hcoord]
    push_cast at hj ⊢
    omega
  rw [h1, h2]
  norm_num

/-- `∑_{{x,y}} |g_R(y) - g_R(x)| ≤ 4 d^{3/2} √R` (`orrw.tex`). -/
theorem gR_tv_bound (hd : 0 < d) (R : ℕ) :
    (∑' p : Site d × Fin d, |gR R (p.1 + dirVec (p.2, true)) - gR R p.1|)
      ≤ 4 * (d : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (R : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [tsum_eq_sum (s := box d (R + 1) ×ˢ (Finset.univ : Finset (Fin d)))
    fun _ hp => gR_grad_eq_zero_of_notMem hp, Finset.sum_product]
  have hstep : ∀ x ∈ box d (R + 1), ∀ i : Fin d,
      |gR R (x + dirVec ((i, true) : Dir d)) - gR R x|
        ≤ ∑ r ∈ Finset.range R, |Q^[r] (delta0 : Site d → ℝ) (x + dirVec ((i, true) : Dir d))
            - Q^[r] (delta0 : Site d → ℝ) x| := by
    intro x _ i
    unfold gR
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  calc ∑ x ∈ box d (R + 1), ∑ i : Fin d, |gR R (x + dirVec ((i, true) : Dir d)) - gR R x|
      ≤ ∑ x ∈ box d (R + 1), ∑ i : Fin d, ∑ r ∈ Finset.range R,
          |Q^[r] (delta0 : Site d → ℝ) (x + dirVec ((i, true) : Dir d))
            - Q^[r] (delta0 : Site d → ℝ) x| :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun i _ => hstep x hx i
    _ = ∑ i : Fin d, ∑ r ∈ Finset.range R, ∑ x ∈ box d (R + 1),
          |Q^[r] (delta0 : Site d → ℝ) (x + dirVec ((i, true) : Dir d))
            - Q^[r] (delta0 : Site d → ℝ) x| := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ ≤ ∑ _i : Fin d, ∑ r ∈ Finset.range R,
          2 * (Real.sqrt (d : ℝ) / Real.sqrt ((r : ℝ) + 1)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun r hr =>
          sum_box_abs_diff_iterate_le hd (by
            have := Finset.mem_range.mp hr
            omega) i
    _ = (d : ℝ) * (2 * Real.sqrt (d : ℝ)
          * ∑ r ∈ Finset.range R, (1 : ℝ) / Real.sqrt ((r : ℝ) + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring
    _ ≤ (d : ℝ) * (2 * Real.sqrt (d : ℝ) * (2 * Real.sqrt (R : ℝ))) := by
        have h1 : (0 : ℝ) ≤ 2 * Real.sqrt (d : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (sum_inv_sqrt_le R) h1) (le_of_lt hdR)
    _ = 4 * (d : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (R : ℝ) := by
        rw [rpow_three_halves]
        ring

end ORRW
