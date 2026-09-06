/-
The one-dimensional lazy walk kernel, used by Section 8 of `orrw.tex`.

The proof of `lem:green` (`orrw.tex`) realizes a step of the lazy walk
`Q` on `ℤ^d` by choosing a coordinate uniformly and taking a lazy step in it,
staying with probability `1/2` and moving either way with probability `1/4`.
The `m`-step law of that one-dimensional walk is

  `p_m(k) = 4^{-m} binom(2m, m+k)`,

which is what `ORRW.P1` is.  The paper uses four properties of it: it is a
probability distribution, it is symmetric and unimodal, its maximum
`p_m(0)` is at most `(m+1)^{-1/2}`, and consequently
`∑_k |p_m(k+1) - p_m(k)| = 2 p_m(0)`.
-/
import Mathlib
import ORRW.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

/-! ### Binomial coefficients with an integer lower index -/

/-- `binom n j` for an integer `j`, extended by `0` to `j < 0`.  `Nat.choose`
already vanishes for `j > n`. -/
noncomputable def binomZ (n : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j then (n.choose j.toNat : ℝ) else 0

/-- The one-dimensional lazy walk's step law assigns nonnegative weight to every site, the basic positivity fact underlying its use as a probability distribution. -/
lemma binomZ_nonneg (n : ℕ) (j : ℤ) : 0 ≤ binomZ n j := by
  unfold binomZ; split <;> positivity

/-- Provides the vanishing of the one-dimensional lazy walk kernel at negative sites, so the distribution can be summed over all of ℤ without case analysis. -/
lemma binomZ_of_neg {n : ℕ} {j : ℤ} (h : j < 0) : binomZ n j = 0 := by
  unfold binomZ; rw [if_neg (by omega)]

/-- Bridges the integer-valued binomial coefficient to its natural-number counterpart so the one-dimensional walk probabilities can be handled with standard binomial estimates. -/
lemma binomZ_natCast (n j : ℕ) : binomZ n (j : ℤ) = (n.choose j : ℝ) := by
  unfold binomZ; rw [if_pos (by positivity)]; simp

/-- The one-dimensional lazy walk's step law vanishes outside its range, since the generalized binomial coefficient is zero when the offset exceeds the number of steps. -/
lemma binomZ_of_lt {n : ℕ} {j : ℤ} (h : (n : ℤ) < j) : binomZ n j = 0 := by
  have hj : 0 ≤ j := by omega
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, j = (t : ℤ) := ⟨j.toNat, by omega⟩
  rw [binomZ_natCast]
  have : n < t := by exact_mod_cast h
  simp [Nat.choose_eq_zero_of_lt this]

/-- Records the Pascal-style recurrence for the one-dimensional lazy walk kernel, letting the m-step law be built up inductively for the Section 8 estimates. -/
lemma binomZ_succ (n : ℕ) (j : ℤ) : binomZ (n + 1) j = binomZ n (j - 1) + binomZ n j := by
  rcases lt_trichotomy j 0 with h | h | h
  · rw [binomZ_of_neg h, binomZ_of_neg (by omega), binomZ_of_neg h]; ring
  · subst h
    rw [binomZ_of_neg (by norm_num : (0 : ℤ) - 1 < 0),
      show (0 : ℤ) = ((0 : ℕ) : ℤ) from by norm_num, binomZ_natCast, binomZ_natCast]
    simp
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, j = (t : ℕ) + 1 := ⟨(j - 1).toNat, by omega⟩
    have h1 : ((t : ℤ) + 1) - 1 = (t : ℤ) := by ring
    have h2 : ((t : ℤ) + 1) = ((t + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, h2, binomZ_natCast, binomZ_natCast, binomZ_natCast]
    rw [Nat.choose_succ_succ]
    push_cast; ring

/-- Symmetry of the one-dimensional lazy walk kernel, reflecting the index about the midpoint of its range. -/
lemma binomZ_symm (n : ℕ) (j : ℤ) : binomZ n ((n : ℤ) - j) = binomZ n j := by
  rcases lt_trichotomy j 0 with h | h | h
  · rw [binomZ_of_neg h, binomZ_of_lt (by omega)]
  · subst h
    rw [show (n : ℤ) - 0 = ((n : ℕ) : ℤ) from by ring, binomZ_natCast,
      show (0 : ℤ) = ((0 : ℕ) : ℤ) from by norm_num, binomZ_natCast]
    simp
  · by_cases hjn : (n : ℤ) < j
    · rw [binomZ_of_lt hjn, binomZ_of_neg (by omega)]
    · push_neg at hjn
      obtain ⟨t, rfl⟩ : ∃ t : ℕ, j = (t : ℤ) := ⟨j.toNat, by omega⟩
      have htn : t ≤ n := by exact_mod_cast hjn
      have : (n : ℤ) - (t : ℤ) = ((n - t : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub htn]; ring
      rw [this, binomZ_natCast, binomZ_natCast, Nat.choose_symm htn]

/-- The middle binomial coefficient is the largest. -/
lemma binomZ_le_middle (m : ℕ) (j : ℤ) : binomZ (2 * m) j ≤ binomZ (2 * m) (m : ℤ) := by
  have hmid : binomZ (2 * m) (m : ℤ) = ((2 * m).choose m : ℝ) := binomZ_natCast _ _
  rcases lt_or_ge j 0 with h | h
  · rw [binomZ_of_neg h, hmid]; positivity
  · obtain ⟨t, rfl⟩ : ∃ t : ℕ, j = (t : ℤ) := ⟨j.toNat, by omega⟩
    rw [binomZ_natCast, hmid]
    have := Nat.choose_le_middle t (2 * m)
    have h2 : 2 * m / 2 = m := by omega
    rw [h2] at this
    exact_mod_cast this

/-- On the right half the binomial coefficients decrease. -/
lemma binomZ_antitone (m : ℕ) {j : ℤ} (h : (m : ℤ) ≤ j) :
    binomZ (2 * m) (j + 1) ≤ binomZ (2 * m) j := by
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, j = (t : ℤ) := ⟨j.toNat, by omega⟩
  have hmt : m ≤ t := by exact_mod_cast h
  by_cases hle : t + 1 ≤ 2 * m
  · have e1 : ((t : ℤ) + 1) = ((t + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, binomZ_natCast, binomZ_natCast]
    have hr : 2 * m - (t + 1) < 2 * m / 2 := by omega
    have key := Nat.choose_le_succ_of_lt_half_left (n := 2 * m) (r := 2 * m - (t + 1)) hr
    have e2 : 2 * m - (t + 1) + 1 = 2 * m - t := by omega
    rw [e2] at key
    rw [Nat.choose_symm hle, Nat.choose_symm (by omega : t ≤ 2 * m)] at key
    exact_mod_cast key
  · have : ((2 * m : ℕ) : ℤ) < (t : ℤ) + 1 := by push_cast; omega
    rw [binomZ_of_lt this]
    exact binomZ_nonneg _ _

/-! ### The one-dimensional lazy kernel -/

/-- `P1 m k = 4^{-m} binom(2m, m+k)` is the `m`-step law of the lazy walk on
`ℤ` that stays with probability `1/2` and moves either way with probability
`1/4`. -/
noncomputable def P1 (m : ℕ) (k : ℤ) : ℝ := binomZ (2 * m) ((m : ℤ) + k) / 4 ^ m

/-- The one-dimensional lazy walk kernel is a probability weight, being nonnegative at every site. -/
lemma P1_nonneg (m : ℕ) (k : ℤ) : 0 ≤ P1 m k :=
  div_nonneg (binomZ_nonneg _ _) (by positivity)

/-- The zero-step law of the one-dimensional lazy walk is a point mass at the origin, anchoring the inductive description of the kernel. -/
lemma P1_zero_step (k : ℤ) : P1 0 k = if k = 0 then 1 else 0 := by
  have h : P1 0 k = binomZ 0 k := by
    unfold P1; norm_num
  rw [h]
  unfold binomZ
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [if_neg (by omega), if_neg (by omega)]
  · subst hk; norm_num
  · rw [if_pos (by omega), if_neg (by omega),
      Nat.choose_eq_zero_of_lt (by omega : 0 < k.toNat)]
    norm_num

/-- The lazy one-step recursion, which is what makes `P1` the law of the lazy
walk: `p_{m+1}(k) = p_m(k)/2 + p_m(k-1)/4 + p_m(k+1)/4`. -/
lemma P1_succ (m : ℕ) (k : ℤ) :
    P1 (m + 1) k = P1 m k / 2 + P1 m (k - 1) / 4 + P1 m (k + 1) / 4 := by
  have hpow : (4 : ℝ) ^ (m + 1) = 4 ^ m * 4 := by ring
  have e : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
  have key : binomZ (2 * (m + 1)) (((m : ℤ) + 1) + k)
      = 2 * binomZ (2 * m) ((m : ℤ) + k) + binomZ (2 * m) ((m : ℤ) + (k - 1))
        + binomZ (2 * m) ((m : ℤ) + (k + 1)) := by
    rw [e, binomZ_succ, binomZ_succ, binomZ_succ]
    have a1 : ((m : ℤ) + 1 + k) - 1 - 1 = (m : ℤ) + (k - 1) := by ring
    have a2 : ((m : ℤ) + 1 + k) - 1 = (m : ℤ) + k := by ring
    have a3 : ((m : ℤ) + 1 + k) = (m : ℤ) + (k + 1) := by ring
    rw [a1, a2, a3]; ring
  unfold P1
  push_cast
  rw [hpow, key]
  field_simp
  ring

/-- Records the symmetry of the one-dimensional lazy walk's step law, so the kernel's mass at −k matches its mass at k. -/
lemma P1_symm (m : ℕ) (k : ℤ) : P1 m (-k) = P1 m k := by
  unfold P1
  congr 1
  have : ((2 * m : ℕ) : ℤ) - ((m : ℤ) + k) = (m : ℤ) + (-k) := by push_cast; ring
  rw [← this, binomZ_symm]

/-- The one-dimensional lazy walk kernel vanishes outside the range where the displacement cannot exceed the number of steps, so the mass is supported on sites within distance m of the origin. -/
lemma P1_eq_zero {m : ℕ} {k : ℤ} (h : (m : ℤ) < |k|) : P1 m k = 0 := by
  unfold P1
  rcases abs_cases k with ⟨hk, _⟩ | ⟨hk, _⟩
  · rw [binomZ_of_lt (by push_cast; omega), zero_div]
  · rw [binomZ_of_neg (by omega), zero_div]

/-- The one-dimensional lazy walk kernel is maximized at the origin, the unimodality used to bound the potential in the green kernel estimate. -/
lemma P1_le_max (m : ℕ) (k : ℤ) : P1 m k ≤ P1 m 0 := by
  unfold P1
  have h0 : (m : ℤ) + 0 = (m : ℤ) := by ring
  have h4 : (0 : ℝ) ≤ ((4 : ℝ) ^ m)⁻¹ := by positivity
  rw [h0]
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right (binomZ_le_middle m ((m : ℤ) + k)) h4

/-- `P1 m` is nonincreasing to the right of the origin. -/
lemma P1_antitone (m : ℕ) {k : ℤ} (h : 0 ≤ k) : P1 m (k + 1) ≤ P1 m k := by
  unfold P1
  have e : (m : ℤ) + (k + 1) = ((m : ℤ) + k) + 1 := by ring
  have h4 : (0 : ℝ) ≤ ((4 : ℝ) ^ m)⁻¹ := by positivity
  rw [e]
  simpa [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right (binomZ_antitone m (by omega : (m : ℤ) ≤ (m : ℤ) + k)) h4

/-- `P1 m` is nondecreasing to the left of the origin. -/
lemma P1_monotone_left (m : ℕ) {k : ℤ} (h : k + 1 ≤ 0) : P1 m k ≤ P1 m (k + 1) := by
  have h1 : P1 m k = P1 m (-k) := (P1_symm m k).symm
  have h2 : P1 m (k + 1) = P1 m (-(k + 1)) := (P1_symm m (k + 1)).symm
  rw [h1, h2]
  have e : -k = -(k + 1) + 1 := by ring
  rw [e]
  exact P1_antitone m (by omega)



/-! ### Total mass -/

/-- The one-dimensional lazy walk mass p_m(k) vanishes off the range of sites reachable in m steps. -/
lemma P1_eq_zero_of_notMem {m : ℕ} {k : ℤ} (h : k ∉ Finset.Icc (-(m : ℤ)) (m : ℤ)) :
    P1 m k = 0 := by
  refine P1_eq_zero ?_
  simp only [Finset.mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · rw [abs_of_nonpos (by omega)]; omega
  · rw [abs_of_nonneg (by omega)]; omega

/-- The one-dimensional lazy walk law is summable, so its total mass and range sums can be handled by infinite-sum machinery. -/
lemma P1_summable (m : ℕ) : Summable (P1 m) :=
  summable_of_ne_finset_zero (s := Finset.Icc (-(m : ℤ)) (m : ℤ))
    fun _ hk => P1_eq_zero_of_notMem hk

/-- Summing the one-dimensional lazy walk weights over the whole range gives the total probability mass, so the distribution property of `p_m` can be used with finite sums. -/
lemma tsum_P1_eq_sum (m : ℕ) :
    ∑' k : ℤ, P1 m k = ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), P1 m k :=
  tsum_eq_sum fun _ hk => P1_eq_zero_of_notMem hk

/-- Shifting the site by a constant leaves the total weight of the one-dimensional lazy walk kernel unchanged, so the kernel sums to one over the whole range. -/
lemma tsum_P1_shift (m : ℕ) (c : ℤ) : ∑' k : ℤ, P1 m (k + c) = ∑' k : ℤ, P1 m k :=
  Equiv.tsum_eq (Equiv.addRight c) (P1 m)

/-- The one-dimensional lazy walk kernel is a probability distribution over its range, the first of the four properties used in the Green function estimate. -/
lemma tsum_P1 (m : ℕ) : ∑' k : ℤ, P1 m k = 1 := by
  induction m with
  | zero =>
    have : ∀ k : ℤ, P1 0 k = if k = 0 then (1 : ℝ) else 0 := P1_zero_step
    simp [this]
  | succ m ih =>
    have hsplit : ∀ k : ℤ,
        P1 (m + 1) k = P1 m (k + 0) / 2 + P1 m (k + (-1)) / 4 + P1 m (k + 1) / 4 := by
      intro k
      have := P1_succ m k
      simp only [add_zero]
      rw [this]
      ring_nf
    have hs0 : Summable (fun k : ℤ => P1 m (k + 0)) :=
      (P1_summable m).comp_injective (add_left_injective (0 : ℤ))
    have hs1 : Summable (fun k : ℤ => P1 m (k + (-1))) :=
      (P1_summable m).comp_injective (add_left_injective (-1 : ℤ))
    have hs2 : Summable (fun k : ℤ => P1 m (k + 1)) :=
      (P1_summable m).comp_injective (add_left_injective (1 : ℤ))
    calc ∑' k : ℤ, P1 (m + 1) k
        = ∑' k : ℤ, (P1 m (k + 0) / 2 + P1 m (k + (-1)) / 4 + P1 m (k + 1) / 4) := by
          exact tsum_congr hsplit
      _ = (∑' k : ℤ, P1 m (k + 0)) / 2 + (∑' k : ℤ, P1 m (k + (-1))) / 4
            + (∑' k : ℤ, P1 m (k + 1)) / 4 := by
          rw [Summable.tsum_add ((hs0.div_const 2).add (hs1.div_const 4)) (hs2.div_const 4),
            Summable.tsum_add (hs0.div_const 2) (hs1.div_const 4), tsum_div_const,
            tsum_div_const, tsum_div_const]
      _ = 1 := by
          rw [tsum_P1_shift, tsum_P1_shift, tsum_P1_shift, ih]; norm_num

/-! ### The maximum -/

/-- Records the value of the one-dimensional lazy walk kernel at the origin, the maximum used to bound the potential in the proof of the Green function estimate. -/
lemma P1_zero_eq (m : ℕ) : P1 m 0 = (Nat.centralBinom m : ℝ) / 4 ^ m := by
  unfold P1 Nat.centralBinom
  rw [show (m : ℤ) + 0 = ((m : ℕ) : ℤ) from by ring, binomZ_natCast]

/-- The central weight of the one-dimensional lazy walk kernel is strictly positive, so it can serve as a probability mass at the origin. -/
lemma P1_zero_pos (m : ℕ) : 0 < P1 m 0 := by
  rw [P1_zero_eq]
  have := Nat.centralBinom_pos m
  positivity

/-- Relates the peak weight of the one-dimensional lazy walk at consecutive times, giving the recurrence needed to bound the maximum by the inverse square root of the time. -/
lemma P1_zero_succ (m : ℕ) : P1 (m + 1) 0 = (2 * m + 1) / (2 * m + 2) * P1 m 0 := by
  have key : ((m : ℝ) + 1) * (Nat.centralBinom (m + 1) : ℝ)
      = 2 * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) := by
    have := Nat.succ_mul_centralBinom_succ m
    have h2 : (((m + 1) * Nat.centralBinom (m + 1) : ℕ) : ℝ)
        = ((2 * (2 * m + 1) * Nat.centralBinom m : ℕ) : ℝ) := by rw [this]
    push_cast at h2
    linarith
  rw [P1_zero_eq, P1_zero_eq]
  have h4 : (0 : ℝ) < 4 ^ m := by positivity
  have hm : (0 : ℝ) < 2 * (m : ℝ) + 2 := by positivity
  have hp : (4 : ℝ) ^ (m + 1) = 4 * 4 ^ m := by ring
  have hR : (2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2) * ((Nat.centralBinom m : ℝ) / 4 ^ m)
      = ((2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ)) / ((2 * (m : ℝ) + 2) * 4 ^ m) :=
    div_mul_div_comm _ _ _ _
  rw [hp, hR, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (2 * (4 : ℝ) ^ m) * key

/-- `p_m(0) ≤ (m+1)^{-1/2}`: the paper's induction from
`p_{m+1}(0)/p_m(0) = (2m+1)/(2m+2)` (`orrw.tex`). -/
lemma P1_zero_le_inv_sqrt (m : ℕ) : P1 m 0 ≤ 1 / Real.sqrt ((m : ℝ) + 1) := by
  induction m with
  | zero =>
    have h0 : P1 0 0 = 1 := by rw [P1_zero_eq]; norm_num [Nat.centralBinom]
    rw [h0]
    norm_num
  | succ m ih =>
    have hs1 : Real.sqrt ((m : ℝ) + 1) > 0 := Real.sqrt_pos.mpr (by positivity)
    have hs2 : Real.sqrt (((m : ℝ) + 1) + 1) > 0 := Real.sqrt_pos.mpr (by positivity)
    have e1 : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 :=
      Real.sq_sqrt (by positivity)
    have e2 : Real.sqrt (((m : ℝ) + 1) + 1) ^ 2 = ((m : ℝ) + 1) + 1 :=
      Real.sq_sqrt (by positivity)
    have hratio : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2) := by positivity
    have hstep : P1 (m + 1) 0 ≤ (2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2) * (1 / Real.sqrt ((m : ℝ) + 1)) := by
      rw [P1_zero_succ]
      exact mul_le_mul_of_nonneg_left ih hratio
    have hfin : (2 * (m : ℝ) + 1) / (2 * (m : ℝ) + 2) * (1 / Real.sqrt ((m : ℝ) + 1))
        ≤ 1 / Real.sqrt (((m : ℝ) + 1) + 1) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hs1, hs2, e1, e2, sq_nonneg (Real.sqrt ((m:ℝ)+1) - Real.sqrt (((m:ℝ)+1)+1)),
        mul_pos hs1 hs2]
    calc P1 (m + 1) 0 ≤ _ := hstep
      _ ≤ 1 / Real.sqrt (((m : ℝ) + 1) + 1) := hfin
      _ = 1 / Real.sqrt (((m + 1 : ℕ) : ℝ) + 1) := by push_cast; ring_nf

/-! ### Total variation of the discrete gradient

`∑_k |p_m(k+1) - p_m(k)| = 2 p_m(0)` (`orrw.tex`), which holds because
`p_m` is symmetric and unimodal, so the sum telescopes on each side of the
origin. -/

private lemma sum_Icc_tele (g : ℤ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (g k - g (k + 1)) = g 0 - g ((n : ℤ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hset : Finset.Icc (0 : ℤ) ((n : ℤ) + 1)
          = insert ((n : ℤ) + 1) (Finset.Icc (0 : ℤ) (n : ℤ)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : ((n : ℤ) + 1) ∉ Finset.Icc (0 : ℤ) (n : ℤ) := by
        simp only [Finset.mem_Icc]; omega
      have hc : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      rw [hc, hset, Finset.sum_insert hnot, ih]
      ring

/-- The total variation of the one-dimensional lazy walk kernel across its range is exactly twice its peak weight at the origin. -/
lemma sum_abs_diff_P1_right (m : ℕ) :
    ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ), |P1 m (k + 1) - P1 m k| = P1 m 0 := by
  have h1 : ∀ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
      |P1 m (k + 1) - P1 m k| = P1 m k - P1 m (k + 1) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have := P1_antitone m hk.1
    rw [abs_of_nonpos (by linarith)]
    ring
  have hz : P1 m ((m : ℤ) + 1) = 0 := by
    refine P1_eq_zero ?_
    rw [abs_of_nonneg (by positivity)]
    omega
  rw [Finset.sum_congr rfl h1, sum_Icc_tele, hz]
  ring

/-- The total variation of the one-dimensional lazy walk kernel over its range equals twice its peak weight at the origin. -/
lemma sum_abs_diff_P1_left (m : ℕ) :
    ∑ k ∈ Finset.Icc (-(m : ℤ) - 1) (-1), |P1 m (k + 1) - P1 m k| = P1 m 0 := by
  rw [← sum_abs_diff_P1_right m]
  refine Finset.sum_nbij' (fun k => -k - 1) (fun l => -l - 1) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a _; ring
  · intro a _; ring
  · intro a _
    have e1 : P1 m ((-a - 1) + 1) = P1 m a := by
      have : (-a - 1) + 1 = -a := by ring
      rw [this, P1_symm]
    have e2 : P1 m (-a - 1) = P1 m (a + 1) := by
      have : -a - 1 = -(a + 1) := by ring
      rw [this, P1_symm]
    rw [e1, e2, abs_sub_comm]

/-- The one-dimensional lazy walk kernel vanishes outside its range, so the total variation sum over adjacent differences only involves sites within the walk's reach. -/
lemma abs_diff_P1_eq_zero_of_notMem {m : ℕ} {k : ℤ}
    (h : k ∉ Finset.Icc (-(m : ℤ) - 1) (m : ℤ)) : |P1 m (k + 1) - P1 m k| = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at h
  have h1 : P1 m k = 0 := by
    refine P1_eq_zero ?_
    rcases h with h | h
    · rw [abs_of_nonpos (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega
  have h2 : P1 m (k + 1) = 0 := by
    refine P1_eq_zero ?_
    rcases h with h | h
    · rw [abs_of_nonpos (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega
  rw [h1, h2]; simp

/-- `∑_k |p_m(k+1) - p_m(k)| = 2 p_m(0)`. -/
lemma tsum_abs_diff_P1 (m : ℕ) : ∑' k : ℤ, |P1 m (k + 1) - P1 m k| = 2 * P1 m 0 := by
  have hsum : ∑' k : ℤ, |P1 m (k + 1) - P1 m k|
      = ∑ k ∈ Finset.Icc (-(m : ℤ) - 1) (m : ℤ), |P1 m (k + 1) - P1 m k| :=
    tsum_eq_sum fun _ hk => abs_diff_P1_eq_zero_of_notMem hk
  have hset : Finset.Icc (-(m : ℤ) - 1) (m : ℤ)
      = Finset.Icc (-(m : ℤ) - 1) (-1) ∪ Finset.Icc (0 : ℤ) (m : ℤ) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc (-(m : ℤ) - 1) (-1)) (Finset.Icc (0 : ℤ) (m : ℤ)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  rw [hsum, hset, Finset.sum_union hdisj, sum_abs_diff_P1_left, sum_abs_diff_P1_right]
  ring

/-- The total variation sum of the one-dimensional lazy walk kernel's successive differences converges, as needed for the variation bound used in the Green function estimate. -/
lemma summable_abs_diff_P1 (m : ℕ) : Summable (fun k : ℤ => |P1 m (k + 1) - P1 m k|) :=
  summable_of_ne_finset_zero (s := Finset.Icc (-(m : ℤ) - 1) (m : ℤ))
    fun _ hk => abs_diff_P1_eq_zero_of_notMem hk

/-! ### Sums over a box large enough to contain the support -/

/-- Supplies the vanishing case of the one-dimensional lazy walk kernel, showing the step mass p_m(k) is zero once the displacement k leaves the reachable range, so sums over a window can be truncated at the exit sites. -/
lemma P1_eq_zero_of_notMem_Icc {m L : ℕ} (hmL : m ≤ L) {k : ℤ}
    (h : k ∉ Finset.Icc (-(L : ℤ)) (L : ℤ)) : P1 m k = 0 := by
  refine P1_eq_zero ?_
  simp only [Finset.mem_Icc, not_and_or, not_le] at h
  have hL : (m : ℤ) ≤ (L : ℤ) := by exact_mod_cast hmL
  rcases h with h | h
  · rw [abs_of_nonpos (by omega)]; omega
  · rw [abs_of_nonneg (by omega)]; omega

/-- Bounds the total one-dimensional walk weight over a finite interval of sites, providing the truncated range estimate needed when the exit-time analysis restricts the kernel to sites within distance L. -/
lemma sum_P1_Icc {m L : ℕ} (hmL : m ≤ L) :
    ∑ k ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), P1 m k = 1 := by
  rw [← tsum_P1 m, tsum_eq_sum (s := Finset.Icc (-(L : ℤ)) (L : ℤ))
    fun _ hk => P1_eq_zero_of_notMem_Icc hmL hk]

/-- The one-dimensional lazy walk kernel vanishes outside the range where its binomial formula applies, so the mass beyond the window of width L contributes nothing once m + 1 ≤ L. -/
lemma abs_diff_P1_eq_zero_of_notMem_Icc {m L : ℕ} (hmL : m + 1 ≤ L) {k : ℤ}
    (h : k ∉ Finset.Icc (-(L : ℤ)) (L : ℤ)) : |P1 m (k + 1) - P1 m k| = 0 := by
  refine abs_diff_P1_eq_zero_of_notMem (m := m) (k := k) ?_
  simp only [Finset.mem_Icc, not_and_or, not_le] at h ⊢
  have hL : (m : ℤ) + 1 ≤ (L : ℤ) := by exact_mod_cast hmL
  omega

/-- Bounds the total variation of the one-dimensional lazy walk kernel over an interval by twice its peak, the estimate needed for the charge comparison at the exit site. -/
lemma sum_abs_diff_P1_Icc {m L : ℕ} (hmL : m + 1 ≤ L) :
    ∑ k ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), |P1 m (k + 1) - P1 m k| = 2 * P1 m 0 := by
  rw [← tsum_abs_diff_P1 m, tsum_eq_sum (s := Finset.Icc (-(L : ℤ)) (L : ℤ))
    fun _ hk => abs_diff_P1_eq_zero_of_notMem_Icc hmL hk]

/-- The maximum of the `m`-step law, in the form used by `lem:green`. -/
lemma two_mul_P1_zero_le (m : ℕ) : 2 * P1 m 0 ≤ 2 / Real.sqrt ((m : ℝ) + 1) := by
  have h := P1_zero_le_inv_sqrt m
  rw [div_eq_mul_inv]
  rw [one_div] at h
  linarith

end ORRW
