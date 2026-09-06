/-
Theorem 1.1 of Bou-Rabee--Peres (`thm:main`, `orrw.tex`): the expected
range.  Markov's inequality inverts the optional-stopping bound
`E_β[σ_k ∧ n] ≤ Kβk^{1+1/d}` of `ORRW.Support.expect_min_sigma_le`.

Nothing in this file is frozen.
-/
import ORRW.Support.OptionalStopping

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW.Support

open Finset ORRW

variable {d : ℕ}

/-! ### Elementary facts about `prb` and `expect` -/

/-- The expectation of the constant `1`. -/
theorem expect_one {N : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) :
    expect (d := d) N β (fun _ => (1 : ℝ)) = 1 := by
  unfold expect
  simpa using sum_prob_eq_one hd hβ N

/-- An event and its complement have total probability one. -/
theorem prb_add_compl {N : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β)
    (P : (Fin N → Dir d) → Prop) :
    prb N β P + prb N β (fun w => ¬ P w) = 1 := by
  classical
  unfold prb
  rw [← Finset.sum_add_distrib]
  refine Eq.trans (Finset.sum_congr rfl fun w _ => ?_) (sum_prob_eq_one hd hβ N)
  by_cases h : P w
  · simp [h]
  · simp [h]

/-- Markov's inequality: `t·P{f ≥ t} ≤ E f` for a nonnegative `f`. -/
theorem mul_prb_le_expect {N : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β)
    (f : (Fin N → Dir d) → ℝ) (hf : ∀ w, 0 ≤ f w) (t : ℝ) :
    t * prb N β (fun w => t ≤ f w) ≤ expect N β f := by
  classical
  unfold prb expect
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  by_cases h : t ≤ f w
  · rw [if_pos h, show t * (prob β w * 1) = prob β w * t by ring]
    exact mul_le_mul_of_nonneg_left h (prob_pos hd hβ w).le
  · rw [if_neg h, show t * (prob β w * 0) = 0 by ring]
    exact mul_nonneg (prob_pos hd hβ w).le (hf w)

/-- A probability is the expectation of the indicator of its event. -/
theorem prb_eq_expect_indicator {N : ℕ} (β : ℝ) (P : (Fin N → Dir d) → Prop)
    [DecidablePred P] :
    prb N β P = expect N β (fun w => if P w then (1 : ℝ) else 0) := by
  classical
  unfold prb expect
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : P w <;> simp [h]

/-- `E_β` commutes with a finite sum. -/
theorem expect_sum {N : ℕ} (β : ℝ) (s : Finset ℕ) (f : ℕ → (Fin N → Dir d) → ℝ) :
    ∑ m ∈ s, expect N β (f m) = expect N β (fun w => ∑ m ∈ s, f m w) := by
  unfold expect
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ => by rw [Finset.mul_sum]

/-- `E_β` respects pointwise equality. -/
theorem expect_congr {N : ℕ} (β : ℝ) {f g : (Fin N → Dir d) → ℝ} (h : ∀ w, f w = g w) :
    expect N β f = expect N β g := by
  unfold expect
  exact Finset.sum_congr rfl fun w _ => by rw [h w]

/-! ### `⌊a⌋₊ ≥ a/2` for `a ≥ 1` -/

/-- A small arithmetic helper converting the optional-stopping bound on the expected exit time into a floor inequality for the range estimate. -/
theorem half_le_floor {a : ℝ} (ha : 1 ≤ a) : a / 2 ≤ (⌊a⌋₊ : ℝ) := by
  have h1 : (1 : ℝ) ≤ (⌊a⌋₊ : ℝ) := by
    have : 1 ≤ ⌊a⌋₊ := Nat.one_le_floor_iff a |>.mpr ha
    exact_mod_cast this
  have h2 : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  linarith

/-! ### The Markov step

`orrw.tex`: with `a := (n/(2Kβ))^{d/(d+1)}` and `k := ⌊a⌋`, the bound
`E_β[σ_k ∧ n] ≤ Kβk^{1+1/d} ≤ n/2` makes `P_β{σ_k ≤ n} ≥ 1/2`, and
`eq:sigma-range` with `eq:edges-sites` turns that event into `{|R_n| ≥ k/d}`,
which contains `{|R_n| ≥ a/(2d)}`. -/

/-- `P_β{|R_n| ≥ a/(2d)} ≥ 1/2` for `a = (n/(2Kβ))^{d/(d+1)}`, whenever
`n ≥ 2Kβ`. -/
theorem half_le_prb_range (hd : 2 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, 2 * K * β ≤ (n : ℝ) →
      (1 : ℝ) / 2 ≤ prb (d := d) n β (fun w =>
        ((n : ℝ) / (2 * K * β)) ^ ((d : ℝ) / ((d : ℝ) + 1)) / (2 * (d : ℝ))
          ≤ ((R w n).card : ℝ)) := by
  have hd1 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdRpos : (0 : ℝ) < (d : ℝ) := by linarith
  obtain ⟨K, hKpos, hK⟩ := expect_min_sigma_le hd
  refine ⟨K, hKpos, ?_⟩
  set e : ℝ := (d : ℝ) / ((d : ℝ) + 1) with he
  have hepos : (0 : ℝ) < e := by rw [he]; positivity
  have hA : (0 : ℝ) < 2 * K := by linarith
  intro β hβ n hcase
  have hβpos : (0 : ℝ) < β := lt_of_lt_of_le one_pos hβ
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hAB : (0 : ℝ) < 2 * K * β := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hAB hcase
  obtain ⟨a, ha⟩ : ∃ x : ℝ, x = ((n : ℝ) / (2 * K * β)) ^ e := ⟨_, rfl⟩
  rw [← ha]
  have ha0 : (0 : ℝ) ≤ a := by rw [ha]; exact Real.rpow_nonneg (by positivity) e
  have hage1 : (1 : ℝ) ≤ a := by
    rw [ha]
    have hx : (1 : ℝ) ≤ (n : ℝ) / (2 * K * β) := (one_le_div hAB).mpr hcase
    have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hx hepos.le
    rwa [Real.one_rpow] at this
  obtain ⟨k, hk⟩ : ∃ m : ℕ, m = ⌊a⌋₊ := ⟨_, rfl⟩
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkle : (k : ℝ) ≤ a := by rw [hk]; exact Nat.floor_le (by linarith)
  have hkge : a / 2 ≤ (k : ℝ) := by rw [hk]; exact half_le_floor hage1
  -- `Kβk^{1+1/d} ≤ n/2`.
  have hexpo : e * (1 + (1 : ℝ) / (d : ℝ)) = 1 := by
    rw [he]
    have hd0 : (d : ℝ) ≠ 0 := by linarith
    have hd1' : (d : ℝ) + 1 ≠ 0 := by linarith
    field_simp
  have hapow : a ^ (1 + (1 : ℝ) / (d : ℝ)) = (n : ℝ) / (2 * K * β) := by
    rw [ha, ← Real.rpow_mul (by positivity), hexpo, Real.rpow_one]
  have hbound : K * β * (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) ≤ (n : ℝ) / 2 := by
    have hkpow : (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) ≤ (n : ℝ) / (2 * K * β) := by
      rw [← hapow]
      exact Real.rpow_le_rpow hkR hkle (by positivity)
    have hKβ : (0 : ℝ) < K * β := by positivity
    have hmul := mul_le_mul_of_nonneg_left hkpow hKβ.le
    have heq : K * β * ((n : ℝ) / (2 * K * β)) = (n : ℝ) / 2 := by field_simp
    linarith [hmul, heq.le, heq.ge]
  -- Markov on the stopped time.
  have hstop := hK β hβ k n
  have hmk := mul_prb_le_expect (N := n) hd1 hβ
    (fun w => ((min (sigma w k) n : ℕ) : ℝ)) (fun w => Nat.cast_nonneg _) (n : ℝ)
  have hhalf : prb (d := d) n β
      (fun w => (n : ℝ) ≤ ((min (sigma w k) n : ℕ) : ℝ)) ≤ 1 / 2 := by
    have hle : (n : ℝ) * prb (d := d) n β
        (fun w => (n : ℝ) ≤ ((min (sigma w k) n : ℕ) : ℝ)) ≤ (n : ℝ) / 2 := by
      linarith [hmk, hstop, hbound]
    nlinarith [hle, hnpos]
  -- The bad event forces `n < σ_k`.
  have hakd : a / (2 * (d : ℝ)) ≤ (k : ℝ) / (d : ℝ) := by
    rw [div_le_div_iff₀ (by linarith) hdRpos]
    nlinarith [hkge, hdRpos]
  have hincl : prb (d := d) n β (fun w => ¬ (a / (2 * (d : ℝ)) ≤ ((R w n).card : ℝ)))
      ≤ prb (d := d) n β (fun w => (n : ℝ) ≤ ((min (sigma w k) n : ℕ) : ℝ)) := by
    refine prb_mono hd1 hβ _ _ ?_
    intro w hw
    push_neg at hw
    have hlt : (d : ℝ) * ((R w n).card : ℝ) < (k : ℝ) := by
      have hw' : ((R w n).card : ℝ) < (k : ℝ) / (d : ℝ) := lt_of_lt_of_le hw hakd
      rw [lt_div_iff₀ hdRpos] at hw'
      linarith
    have hltN : d * (R w n).card < k := by exact_mod_cast hlt
    have hEle : (E w n).card < k :=
      lt_of_le_of_lt (ORRW.card_edges_le_card_range w n) hltN
    have hnot : ¬ (sigma w k ≤ n) := by
      intro hc
      exact absurd ((sigma_le_iff w (le_refl n)).mp hc) (by omega)
    have hmin : min (sigma w k) n = n := by omega
    rw [hmin]
  have := prb_add_compl (N := n) hd1 hβ
    (fun w => a / (2 * (d : ℝ)) ≤ ((R w n).card : ℝ))
  linarith [hincl, hhalf, this]

/-! ### Theorem 1.1 -/

/-- `E_β|R_n| ≥ cβ^{-d/(d+1)}n^{d/(d+1)}`, the paper's `eq:main-range`. -/
theorem range_lower_bound_of (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ,
      c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))
        ≤ expect (d := d) n β (fun w => ((R w n).card : ℝ)) := by
  have hd1 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  obtain ⟨K, hKpos, hhalf⟩ := half_le_prb_range hd
  set e : ℝ := (d : ℝ) / ((d : ℝ) + 1) with he
  have hepos : (0 : ℝ) < e := by rw [he]; positivity
  have hA : (0 : ℝ) < 2 * K := by linarith
  have hcpos : (0 : ℝ) < (2 * K) ^ (-e) / (4 * (d : ℝ)) :=
    div_pos (Real.rpow_pos_of_pos hA _) (by linarith)
  refine ⟨(2 * K) ^ (-e) / (4 * (d : ℝ)), hcpos, ?_⟩
  intro β hβ n
  have hβpos : (0 : ℝ) < β := lt_of_lt_of_le one_pos hβ
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hAB : (0 : ℝ) < 2 * K * β := by positivity
  obtain ⟨a, ha⟩ : ∃ x : ℝ, x = ((n : ℝ) / (2 * K * β)) ^ e := ⟨_, rfl⟩
  have ha0 : (0 : ℝ) ≤ a := by rw [ha]; exact Real.rpow_nonneg (by positivity) e
  -- The constant is exactly `a/(4d)`.
  have hid : (2 * K) ^ (-e) / (4 * (d : ℝ)) * β ^ (-e) * (n : ℝ) ^ e = a / (4 * (d : ℝ)) := by
    rw [ha, Real.div_rpow hn0 hAB.le, Real.mul_rpow hA.le hβpos.le,
      Real.rpow_neg hA.le, Real.rpow_neg hβpos.le]
    have h1 : ((2 * K) ^ e) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hA e)
    have h2 : (β ^ e) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hβpos e)
    field_simp
  rw [hid]
  by_cases hcase : 2 * K * β ≤ (n : ℝ)
  · -- The main case `a ≥ 1`.
    have hgood := hhalf β hβ n hcase
    rw [← ha] at hgood
    have hfinal := mul_prb_le_expect (N := n) hd1 hβ
      (fun w => ((R w n).card : ℝ)) (fun w => Nat.cast_nonneg _) (a / (2 * (d : ℝ)))
    have had0 : (0 : ℝ) ≤ a / (2 * (d : ℝ)) := by positivity
    have hstep : a / (2 * (d : ℝ)) * (1 / 2)
        ≤ expect (d := d) n β (fun w => ((R w n).card : ℝ)) :=
      le_trans (mul_le_mul_of_nonneg_left hgood had0) hfinal
    have hlast : a / (4 * (d : ℝ)) = a / (2 * (d : ℝ)) * (1 / 2) := by
      field_simp
      ring
    linarith [hstep, hlast.le, hlast.ge]
  · -- The degenerate case `a < 1`.
    push_neg at hcase
    have hale : a ≤ 1 := by
      rw [ha]
      refine Real.rpow_le_one (by positivity) ?_ hepos.le
      rw [div_le_one hAB]
      linarith
    have hone : (1 : ℝ) ≤ expect (d := d) n β (fun w => ((R w n).card : ℝ)) := by
      have hmono := expect_mono (N := n) hd1 hβ (fun _ => (1 : ℝ))
        (fun w => ((R w n).card : ℝ)) (fun w => by
          show (1 : ℝ) ≤ ((R w n).card : ℝ)
          have : 1 ≤ (R w n).card := Finset.card_pos.mpr (R_nonempty w n)
          exact_mod_cast this)
      rwa [expect_one hd1 hβ] at hmono
    have hsmall : a / (4 * (d : ℝ)) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith

end ORRW.Support
