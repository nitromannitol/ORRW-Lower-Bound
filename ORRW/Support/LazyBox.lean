/-
Sums of the product kernel over a box, and the two per-step estimates of
`lem:green` that follow from them.

Everything in Section 8 is supported in a finite box, so a sum "over all of
`ℤ^d`" is a `Finset` sum over `ORRW.box d L` for any `L` large enough, and the
product structure of `ORRW.K` turns it into a product of one-dimensional sums
(`Finset.prod_univ_sum`).
-/
import Mathlib
import ORRW.Support.LazyDecomp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

variable {d : ℕ}

private lemma cnt_le_box {r : ℕ} (c : Fin r → Fin d) (i : Fin d) : cnt c i ≤ r := by
  unfold cnt
  calc ∑ t : Fin r, (if c t = i then 1 else 0)
      ≤ ∑ _t : Fin r, 1 := Finset.sum_le_sum fun t _ => by split <;> omega
    _ = r := by simp

/-- Identifies the sum of the product kernel over a finite box with a product of one-dimensional sums, the reduction underlying the per-step estimates in Section 8. -/
lemma box_eq (d L : ℕ) :
    box d L = Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ)) := rfl

/-! ### The product kernel is a probability distribution -/

/-- The product kernel vanishes at any site outside the box, so sums over all of ℤ^d can be replaced by finite sums over the box. -/
lemma K_eq_zero_of_notMem_box {L : ℕ} {n : Fin d → ℕ} (h : ∀ i, n i ≤ L) {x : Site d}
    (hx : x ∉ box d L) : K n x = 0 := by
  obtain ⟨i, hi⟩ := exists_of_notMem_box hx
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  refine P1_eq_zero (lt_of_le_of_lt ?_ hi)
  exact_mod_cast h i

/-- Upper-bounds the total weight of the product kernel over a finite box by a product of one-dimensional sums, giving the constant behind the per-step estimates in the proof of the green lemma. -/
lemma sum_K_box {L : ℕ} (n : Fin d → ℕ) (h : ∀ i, n i ≤ L) :
    ∑ x ∈ box d L, K n x = 1 := by
  rw [box_eq]
  simp only [K]
  rw [← Finset.prod_univ_sum (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ))
    (fun (i : Fin d) (k : ℤ) => P1 (n i) k)]
  exact Finset.prod_eq_one fun i _ => sum_P1_Icc (h i)

/-! ### The gradient of the product kernel -/

/-- The product kernel changes between adjacent sites only through the one-dimensional factor in the direction of the step, reducing the difference to a single coordinate potential. -/
lemma abs_diff_K_eq {n : Fin d → ℕ} (x : Site d) (i₀ : Fin d) :
    |K n (x + dirVec ((i₀, true) : Dir d)) - K n x|
      = |P1 (n i₀) (x i₀ + 1) - P1 (n i₀) (x i₀)|
        * ∏ j ∈ Finset.univ.erase i₀, P1 (n j) (x j) := by
  rw [K_shift_pos, K_eq_mul_erase n x i₀, ← sub_mul, abs_mul,
    abs_of_nonneg (Finset.prod_nonneg fun j _ => P1_nonneg _ _)]

/-- Bounds the sum of the absolute value of the product kernel over a finite box, providing the finite-volume estimate underlying the per-step bounds in the proof of the green function lemma. -/
lemma sum_abs_diff_K_box {L : ℕ} (n : Fin d → ℕ) (i₀ : Fin d) (h : ∀ i, n i + 1 ≤ L) :
    ∑ x ∈ box d L, |K n (x + dirVec ((i₀, true) : Dir d)) - K n x| = 2 * P1 (n i₀) 0 := by
  classical
  let f : (i : Fin d) → ℤ → ℝ := fun i k =>
    if i = i₀ then |P1 (n i) (k + 1) - P1 (n i) k| else P1 (n i) k
  have hf0 : ∀ k : ℤ, f i₀ k = |P1 (n i₀) (k + 1) - P1 (n i₀) k| := fun _ => if_pos rfl
  have hfn : ∀ i : Fin d, i ≠ i₀ → ∀ k : ℤ, f i k = P1 (n i) k := fun _ hi _ => if_neg hi
  have hpt : ∀ x : Site d,
      |K n (x + dirVec ((i₀, true) : Dir d)) - K n x| = ∏ i, f i (x i) := by
    intro x
    rw [abs_diff_K_eq x i₀,
      ← Finset.mul_prod_erase Finset.univ (fun i => f i (x i)) (Finset.mem_univ i₀), hf0]
    congr 1
    exact (Finset.prod_congr rfl fun j hj => hfn j (Finset.ne_of_mem_erase hj) (x j)).symm
  rw [Finset.sum_congr rfl fun x _ => hpt x, box_eq,
    ← Finset.prod_univ_sum (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ)) f,
    ← Finset.mul_prod_erase Finset.univ
      (fun i => ∑ k ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), f i k) (Finset.mem_univ i₀)]
  have h0 : ∑ k ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), f i₀ k = 2 * P1 (n i₀) 0 := by
    rw [Finset.sum_congr rfl fun k _ => hf0 k]
    exact sum_abs_diff_P1_Icc (h i₀)
  have h1 : ∀ i ∈ Finset.univ.erase i₀,
      ∑ k ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), f i k = 1 := by
    intro i hi
    rw [Finset.sum_congr rfl fun k _ => hfn i (Finset.ne_of_mem_erase hi) k]
    exact sum_P1_Icc (le_trans (Nat.le_succ _) (h i))
  rw [h0, Finset.prod_congr rfl h1, Finset.prod_const_one, mul_one]

/-! ### The two per-step estimates -/

/-- The `r`-step kernel is bounded by the schedule average of `∏_i (N_i+1)^{-1/2}`. -/
lemma iterate_delta0_le_sched (hd : 0 < d) (r : ℕ) (x : Site d) :
    Q^[r] (delta0 : Site d → ℝ) x
      ≤ (∑ c : Fin r → Fin d, ∏ i, (1 : ℝ) / Real.sqrt ((cnt c i : ℝ) + 1)) / (d : ℝ) ^ r := by
  have hdR : (0 : ℝ) < (d : ℝ) ^ r := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  rw [iterate_delta0_eq hd r x, div_le_div_iff_of_pos_right hdR]
  refine Finset.sum_le_sum fun c _ => ?_
  refine Finset.prod_le_prod (fun i _ => P1_nonneg _ _) fun i _ => ?_
  exact le_trans (P1_le_max _ _) (P1_zero_le_inv_sqrt _)

/-- The total variation of the `r`-step kernel along one coordinate, over a box
large enough to contain its support. -/
lemma sum_box_abs_diff_iterate (hd : 0 < d) {r L : ℕ} (hrL : r + 1 ≤ L) (i₀ : Fin d) :
    ∑ x ∈ box d L, |Q^[r] (delta0 : Site d → ℝ) (x + dirVec ((i₀, true) : Dir d))
        - Q^[r] (delta0 : Site d → ℝ) x|
      ≤ (∑ c : Fin r → Fin d, 2 * P1 (cnt c i₀) 0) / (d : ℝ) ^ r := by
  have hdR : (0 : ℝ) < (d : ℝ) ^ r := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  have hbound : ∀ x : Site d,
      |Q^[r] (delta0 : Site d → ℝ) (x + dirVec ((i₀, true) : Dir d))
          - Q^[r] (delta0 : Site d → ℝ) x|
        ≤ (∑ c : Fin r → Fin d,
            |K (cnt c) (x + dirVec ((i₀, true) : Dir d)) - K (cnt c) x|) / (d : ℝ) ^ r := by
    intro x
    rw [iterate_delta0_eq hd r _, iterate_delta0_eq hd r x, div_sub_div_same, abs_div,
      abs_of_pos hdR, div_le_div_iff_of_pos_right hdR, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  refine le_trans (Finset.sum_le_sum fun x _ => hbound x) ?_
  rw [← Finset.sum_div, Finset.sum_comm]
  refine (div_le_div_iff_of_pos_right hdR).mpr ?_
  refine le_of_eq (Finset.sum_congr rfl fun c _ => ?_)
  exact sum_abs_diff_K_box (cnt c) i₀ fun i => by
    have := cnt_le_box c i
    omega

end ORRW
