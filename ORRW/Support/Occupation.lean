/-
The probabilistic half of Theorem 8.2 of `orrw.tex` (`thm:return`).

The compensator identity `eq:compensator` (`orrw.tex`) says that
adding `(β-1) η_{j+1} Δ_j f` to `Δ_j f` restores the weight `β` on the
untraversed edges and leaves a sum that no longer sees the reinforcement.  In
the finite-word model that is the pointwise identity `ORRW.stepWeight_mul_eta`,
and everything else in this file is bookkeeping around it: lifting a one-step
identity to a fixed horizon, telescoping, and the two bounds on
`κ_j = 4dβ/μ_j`.
-/
import Mathlib
import ORRW.Potential
import ORRW.Support.Drift
import ORRW.Support.Conditioning
import ORRW.Support.Poisson
import ORRW.Support.NewEdges
import ORRW.Support.LazyGreenBounds
import ORRW.Support.Return

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

variable {d : ℕ}

/-! ### The two compensated terms -/

/-- `Δ_j f + (β-1) η_{j+1} Δ_j f` for `f = -g_R(· - z)`, the left side of
`eq:compensator`. -/
noncomputable def Aterm {n : ℕ} (β : ℝ) (R : ℕ) (z : Site d) (w : Fin n → Dir d) (j : ℕ) : ℝ :=
  (1 + (β - 1) * eta w (j + 1))
    * (-(gR R (pos w (j + 1) - z)) - -(gR R (pos w j - z)))

/-- `κ_j (1_{{X_j = z}} - Q^R(0, X_j - z))`, the right side of `eq:compensator`
after `eq:poisson`. -/
noncomputable def Bterm {n : ℕ} (β : ℝ) (R : ℕ) (z : Site d) (w : Fin n → Dir d) (j : ℕ) : ℝ :=
  (4 * (d : ℝ) * β / mu β w j)
    * (delta0 (pos w j - z) - Q^[R] (delta0 : Site d → ℝ) (pos w j - z))

/-! ### The compensator identity -/

/-- `orrw.tex`: the step weight times the reinforcement factor is `β`,
whichever kind of edge the step crosses.  This is the whole content of
`eq:compensator`. -/
theorem stepWeight_mul_eta (β : ℝ) {j : ℕ} (v : Fin j → Dir d) (a : Dir d) :
    stepWeight β v j a * (1 + (β - 1) * eta (Fin.snoc v a) (j + 1)) = β := by
  by_cases ha : s(pos v j, pos v j + dirVec a) ∈ E v j
  · rw [ORRW.Support.eta_snoc_of_mem v a ha, show stepWeight β v j a = β by
      unfold stepWeight; rw [if_pos ha]]
    ring
  · rw [ORRW.Support.eta_snoc_of_notMem v a ha, show stepWeight β v j a = 1 by
      unfold stepWeight; rw [if_neg ha]]
    ring

/-- One step of `eq:compensator`, evaluated: the conditional expectation of
`Aterm` given the history `v` is `Bterm`. -/
theorem compensator_step (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) (R : ℕ) (z : Site d)
    {j : ℕ} (v : Fin j → Dir d) :
    ∑ a : Dir d, (stepWeight β v j a / totalWeight β v j) * Aterm β R z (Fin.snoc v a) j
      = Bterm β R z v j := by
  have htw : totalWeight β v j = mu β v j := (mu_eq_totalWeight β v j).symm
  have hmupos : 0 < mu β v j := ORRW.Support.mu_pos hd hβ v j
  have hterm : ∀ a : Dir d,
      (stepWeight β v j a / totalWeight β v j) * Aterm β R z (Fin.snoc v a) j
        = -(β / mu β v j)
          * (gR R ((pos v j - z) + dirVec a) - gR R (pos v j - z)) := by
    intro a
    unfold Aterm
    rw [ORRW.Support.pos_snoc_last v a, ORRW.Support.pos_snoc v a (le_refl j)]
    have hshift : pos v j + dirVec a - z = (pos v j - z) + dirVec a := by abel
    rw [hshift, htw]
    have hkey : stepWeight β v j a * (1 + (β - 1) * eta (Fin.snoc v a) (j + 1)) = β :=
      stepWeight_mul_eta β v a
    field_simp
    linear_combination (-(gR R (pos v j - z + dirVec a)) + gR R (pos v j - z)) * hkey
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.mul_sum,
    sum_dir_gR_diff hd R (pos v j - z)]
  unfold Bterm
  field_simp
  ring

/-! ### Lifting to a fixed horizon -/

/-- Records the initial value of the telescoping A-term at time zero, where no edge has yet been traversed and the compensator correction vanishes. -/
theorem Aterm_init {N : ℕ} (β : ℝ) (R : ℕ) (z : Site d) (w : Fin (N + 1) → Dir d) {j : ℕ}
    (hj : j + 1 ≤ N) : Aterm β R z (Fin.init w) j = Aterm β R z w j := by
  unfold Aterm eta
  simp only [Nat.add_sub_cancel]
  rw [pos_init w hj, pos_init w (by omega : j ≤ N), E_init w hj, E_init w (by omega : j ≤ N)]

/-- Base case of the telescoping bound, fixing the potential term at the initial time when no edge has yet been traversed. -/
theorem Bterm_init {N : ℕ} (β : ℝ) (R : ℕ) (z : Site d) (w : Fin (N + 1) → Dir d) {j : ℕ}
    (hj : j ≤ N) : Bterm β R z (Fin.init w) j = Bterm β R z w j := by
  unfold Bterm mu nu
  rw [pos_init w hj, E_init w hj]

/-- `eq:compensator` at a fixed horizon: the expectations of `Aterm` and `Bterm`
at time `j` agree, for every horizon past `j`. -/
theorem expect_Aterm_eq_Bterm (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) (R : ℕ) (z : Site d)
    (j : ℕ) {N : ℕ} (hN : j + 1 ≤ N) :
    ∑ w : Fin N → Dir d, prob β w * Aterm β R z w j
      = ∑ w : Fin N → Dir d, prob β w * Bterm β R z w j := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [expect_snoc (β := β) (fun w => Aterm β R z w j)]
    have hL : ∑ v : Fin j → Dir d, ∑ a : Dir d,
        prob β v * (stepWeight β v j a / totalWeight β v j) * Aterm β R z (Fin.snoc v a) j
        = ∑ v : Fin j → Dir d, prob β v * Bterm β R z v j := by
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← compensator_step hd hβ R z v, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hL]
    have hR : ∀ w : Fin (j + 1) → Dir d,
        prob β w * Bterm β R z w j = prob β w * Bterm β R z (Fin.init w) j := by
      intro w
      rw [Bterm_init β R z w (le_refl j)]
    rw [Finset.sum_congr rfl fun w _ => hR w]
    exact (expect_init hd hβ (fun v => Bterm β R z v j)).symm
  | succ N hN ih =>
    have hA : ∀ w : Fin (N + 1) → Dir d,
        prob β w * Aterm β R z w j = prob β w * Aterm β R z (Fin.init w) j := by
      intro w; rw [Aterm_init β R z w hN]
    have hB : ∀ w : Fin (N + 1) → Dir d,
        prob β w * Bterm β R z w j = prob β w * Bterm β R z (Fin.init w) j := by
      intro w; rw [Bterm_init β R z w (by omega : j ≤ N)]
    rw [Finset.sum_congr rfl fun w _ => hA w, Finset.sum_congr rfl fun w _ => hB w]
    calc ∑ w : Fin (N + 1) → Dir d, prob β w * Aterm β R z (Fin.init w) j
        = ∑ v : Fin N → Dir d, prob β v * Aterm β R z v j :=
          expect_init hd hβ (fun v => Aterm β R z v j)
      _ = ∑ v : Fin N → Dir d, prob β v * Bterm β R z v j := ih
      _ = ∑ w : Fin (N + 1) → Dir d, prob β w * Bterm β R z (Fin.init w) j :=
          (expect_init hd hβ (fun v => Bterm β R z v j)).symm

/-! ### Telescoping -/

private lemma telescope_Ico (F : ℕ → ℝ) (a k : ℕ) :
    ∑ j ∈ Finset.Ico a (a + k), (F (j + 1) - F j) = F (a + k) - F a := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  have hcong : ∀ i ∈ Finset.range k, F (a + i + 1) - F (a + i)
      = (fun l => F (a + l)) (i + 1) - (fun l => F (a + l)) i := by
    intro i _
    show F (a + i + 1) - F (a + i) = F (a + (i + 1)) - F (a + i)
    rw [show a + (i + 1) = a + i + 1 from by ring]
  rw [Finset.sum_congr rfl hcong, Finset.sum_range_sub (fun l => F (a + l)) k]
  simp

/-- Telescopes the compensator terms over a block of steps into the drop in the potential plus the reinforced edge contribution. -/
theorem sum_Aterm (β : ℝ) (R : ℕ) (z : Site d) {N : ℕ} (w : Fin N → Dir d) (a k : ℕ) :
    ∑ j ∈ Finset.Ico a (a + k), Aterm β R z w j
      = (gR R (pos w a - z) - gR R (pos w (a + k) - z))
        + (β - 1) * ∑ j ∈ Finset.Ico a (a + k), eta w (j + 1)
            * (-(gR R (pos w (j + 1) - z)) - -(gR R (pos w j - z))) := by
  have hsplit : ∀ j : ℕ, Aterm β R z w j
      = (-(gR R (pos w (j + 1) - z)) - -(gR R (pos w j - z)))
        + (β - 1) * (eta w (j + 1)
            * (-(gR R (pos w (j + 1) - z)) - -(gR R (pos w j - z)))) := by
    intro j; unfold Aterm; ring
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, ← Finset.mul_sum,
    telescope_Ico (fun j => -(gR R (pos w j - z))) a k]
  ring

/-! ### The two bounds -/

/-- Basic sanity bound ensuring the resistance-type quantity κ_j stays nonnegative along the walk's range. -/
lemma prob_nonneg (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) {n : ℕ} (w : Fin n → Dir d) :
    0 ≤ prob β w := le_of_lt (prob_pos hd hβ w)

/-- Basic sanity bound ensuring the resistance-type quantity κ_j stays positive throughout the walk, so the compensator estimates below are meaningful. -/
lemma prb_nonneg (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) (n : ℕ)
    (P : (Fin n → Dir d) → Prop) : 0 ≤ prb n β P := by
  classical
  unfold prb
  refine Finset.sum_nonneg fun w _ => mul_nonneg (prob_nonneg hd hβ w) ?_
  split <;> norm_num

/-- A basic bound on the return probabilities κ_j, used as the uniform estimate feeding into the compensator telescoping for Theorem 8.2. -/
lemma prb_le_one (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) (n : ℕ)
    (P : (Fin n → Dir d) → Prop) : prb n β P ≤ 1 := by
  classical
  unfold prb
  calc ∑ w : Fin n → Dir d, prob β w * (if P w then (1 : ℝ) else 0)
      ≤ ∑ w : Fin n → Dir d, prob β w := by
        refine Finset.sum_le_sum fun w _ => ?_
        have h0 := prob_nonneg hd hβ w
        have : (if P w then (1 : ℝ) else 0) ≤ 1 := by split <;> norm_num
        nlinarith
    _ = 1 := sum_prob_eq_one hd hβ n

/-- The pointwise bound on the compensated sum: the oscillation of `g_R` plus
`(β-1)` times its total variation (`orrw.tex`). -/
theorem pointwise_Aterm_bound (hd : 2 ≤ d) {β : ℝ} (hβ : 1 ≤ β) (z : Site d) {N : ℕ}
    (w : Fin N → Dir d) (a k : ℕ) (hN : a + k ≤ N) {R : ℕ} (hR : 1 ≤ R) :
    ∑ j ∈ Finset.Ico a (a + k), Aterm β R z w j
      ≤ (2 + 3 * greenConst d) * (if d = 2 then Real.log ((R : ℝ) + 1) else 1)
        + (β - 1) * (4 * (d : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (R : ℝ)) := by
  have hd0 : 0 < d := by omega
  have hosc := gR_osc_bound (d := d) hd hR (pos w a - z) (pos w (a + k) - z)
  have hgrad : ∑ j ∈ Finset.Ico a (a + k), eta w (j + 1)
      * (-(gR R (pos w (j + 1) - z)) - -(gR R (pos w j - z)))
      ≤ 4 * (d : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (R : ℝ) := by
    have hstep : ∀ j ∈ Finset.Ico a (a + k),
        eta w (j + 1) * (-(gR R (pos w (j + 1) - z)) - -(gR R (pos w j - z)))
          ≤ eta w (j + 1) * |gR R (pos w (j + 1) - z) - gR R (pos w j - z)| := by
      intro j _
      have he : 0 ≤ eta w (j + 1) := by unfold eta; split <;> norm_num
      have hle : -(gR R (pos w (j + 1) - z)) - -(gR R (pos w j - z))
          ≤ |gR R (pos w (j + 1) - z) - gR R (pos w j - z)| := by
        have := neg_abs_le (gR R (pos w (j + 1) - z) - gR R (pos w j - z))
        have := le_abs_self (gR R (pos w (j + 1) - z) - gR R (pos w j - z))
        linarith [abs_nonneg (gR R (pos w (j + 1) - z) - gR R (pos w j - z))]
      exact mul_le_mul_of_nonneg_left hle he
    refine le_trans (Finset.sum_le_sum hstep) ?_
    exact le_trans (sum_eta_grad_le w R z hN) (gR_tv_bound hd0 R)
  have hbeta : (0 : ℝ) ≤ β - 1 := by linarith
  rw [sum_Aterm]
  have := mul_le_mul_of_nonneg_left hgrad hbeta
  linarith

/-- `κ_j ∈ [2, 4d]` for `j ≥ 1`, and `Q^R(0,·) ≤ C R^{-d/2}` (`orrw.tex`). -/
theorem Bterm_lower (hd : 2 ≤ d) {β : ℝ} (hβ : 1 ≤ β) (z : Site d) {N : ℕ}
    (w : Fin N → Dir d) {j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) {R : ℕ} (hR : 1 ≤ R) :
    2 * (if pos w j = z then (1 : ℝ) else 0)
        - 4 * (d : ℝ) * (greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2))
      ≤ Bterm β R z w j := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hβ0 : (0 : ℝ) < β := by linarith
  have hmupos : 0 < mu β w j := ORRW.Support.mu_pos hd0 hβ w j
  have hmule : mu β w j ≤ 2 * (d : ℝ) * β := ORRW.Support.mu_le hβ w j
  have hmuge : β ≤ mu β w j := beta_le_mu hd0 hβ w hj hjN
  have hkappa_lo : (2 : ℝ) ≤ 4 * (d : ℝ) * β / mu β w j := by
    rw [le_div_iff₀ hmupos]
    nlinarith
  have hkappa_hi : 4 * (d : ℝ) * β / mu β w j ≤ 4 * (d : ℝ) := by
    rw [div_le_iff₀ hmupos]
    nlinarith
  have hdelta : (delta0 : Site d → ℝ) (pos w j - z) = if pos w j = z then (1 : ℝ) else 0 := by
    unfold delta0
    by_cases hz : pos w j = z
    · rw [if_pos (by rw [hz]; abel), if_pos hz]
    · rw [if_neg (fun hc => hz (by have := sub_eq_zero.mp hc; exact this)), if_neg hz]
  have hQnn : 0 ≤ Q^[R] (delta0 : Site d → ℝ) (pos w j - z) := iterate_delta0_nonneg R _
  have hQle : Q^[R] (delta0 : Site d → ℝ) (pos w j - z)
      ≤ greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2) := iterate_delta0_sup_bound hd0 hR _
  have hdeltann : (0 : ℝ) ≤ (if pos w j = z then (1 : ℝ) else 0) := by split <;> norm_num
  unfold Bterm
  rw [hdelta, mul_sub]
  have h1 : 2 * (if pos w j = z then (1 : ℝ) else 0)
      ≤ 4 * (d : ℝ) * β / mu β w j * (if pos w j = z then (1 : ℝ) else 0) :=
    mul_le_mul_of_nonneg_right hkappa_lo hdeltann
  have h2 : 4 * (d : ℝ) * β / mu β w j * Q^[R] (delta0 : Site d → ℝ) (pos w j - z)
      ≤ 4 * (d : ℝ) * (greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2)) := by
    refine le_trans (mul_le_mul_of_nonneg_right hkappa_hi hQnn) ?_
    exact mul_le_mul_of_nonneg_left hQle (by positivity)
  linarith

/-! ### The bound of `eq:optimize`, before the choice of `R` -/

/-- The constant multiplying the three terms of `eq:optimize`. -/
noncomputable def occConst (d : ℕ) : ℝ :=
  2 * (d : ℝ) * greenConst d + (2 + 3 * greenConst d) / 2 + 2 * (d : ℝ) ^ ((3 : ℝ) / 2)

/-- The constant appearing in the lower bound on the expected return time is nonnegative, so the eventual bound is meaningful. -/
lemma occConst_nonneg (d : ℕ) : 0 ≤ occConst d := by
  have hg := greenConst_nonneg d
  have h1 : (0 : ℝ) ≤ 2 * (d : ℝ) * greenConst d :=
    mul_nonneg (by positivity) hg
  have h3 : (0 : ℝ) ≤ 2 * (d : ℝ) ^ ((3 : ℝ) / 2) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  unfold occConst
  linarith

/-- Gives the probability that a walk of length n starting at the origin is at site z after j steps, serving as the reference distribution for the compensator bookkeeping. -/
lemma prb_eq_sum {n : ℕ} (β : ℝ) (j : ℕ) (z : Site d) :
    prb n β (fun w => pos w j = z)
      = ∑ w : Fin n → Dir d, prob β w * (if pos w j = z then (1 : ℝ) else 0) := by
  unfold prb
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hc : pos w j = z <;> simp [hc]

/-- Upper-bounds the two-point probability that the walk's range at time j sits at a given site by the resistance term, the second of the two bounds on κ_j needed for Theorem 8.2. -/
lemma two_prb_le (hd : 2 ≤ d) {β : ℝ} (hβ : 1 ≤ β) (z : Site d) {N : ℕ} {j : ℕ}
    (hj : 1 ≤ j) (hjN : j ≤ N) {R : ℕ} (hR : 1 ≤ R) :
    2 * prb N β (fun w => pos w j = z)
        - 4 * (d : ℝ) * (greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2))
      ≤ ∑ w : Fin N → Dir d, prob β w * Bterm β R z w j := by
  have hd0 : 0 < d := by omega
  have hstep : ∀ w : Fin N → Dir d,
      prob β w * (2 * (if pos w j = z then (1 : ℝ) else 0)
          - 4 * (d : ℝ) * (greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2)))
        ≤ prob β w * Bterm β R z w j := fun w =>
    mul_le_mul_of_nonneg_left (Bterm_lower hd hβ z w hj hjN hR) (prob_nonneg hd0 hβ w)
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun w _ => hstep w)
  rw [Finset.sum_congr rfl fun w (_ : w ∈ Finset.univ) =>
    (by ring : prob β w * (2 * (if pos w j = z then (1 : ℝ) else 0)
        - 4 * (d : ℝ) * (greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2)))
      = 2 * (prob β w * (if pos w j = z then (1 : ℝ) else 0))
        - (4 * (d : ℝ) * (greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2))) * prob β w)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_prob_eq_one hd0 hβ N, prb_eq_sum]
  ring

/-- `eq:optimize` of `orrw.tex`, for every truncation `R ≥ 1`. -/
theorem occupation_bound_R (hd : 2 ≤ d) {β : ℝ} (hβ : 1 ≤ β) (z : Site d) (m h : ℕ)
    (hh : 1 ≤ h) {N : ℕ} (hN : m + h ≤ N) {R : ℕ} (hR : 1 ≤ R) :
    ∑ j ∈ Finset.Ico m (m + h), prb N β (fun w => pos w j = z)
      ≤ 1 + occConst d * ((h : ℝ) * (R : ℝ) ^ (-(d : ℝ) / 2)
          + (if d = 2 then Real.log ((R : ℝ) + 1) else 1)
          + (β - 1) * Real.sqrt (R : ℝ)) := by
  classical
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hg := greenConst_nonneg d
  set m' : ℕ := max m 1 with hm'
  have hmm' : m ≤ m' := le_max_left _ _
  have hm'1 : 1 ≤ m' := le_max_right _ _
  have hm'h : m' ≤ m + h := by omega
  set k : ℕ := m + h - m' with hk
  have hkeq : m' + k = m + h := by omega
  -- the head of the window contributes at most one
  have hhead : ∑ j ∈ Finset.Ico m m', prb N β (fun w => pos w j = z) ≤ 1 := by
    have hcard : (Finset.Ico m m').card ≤ 1 := by
      rw [Nat.card_Ico]; omega
    calc ∑ j ∈ Finset.Ico m m', prb N β (fun w => pos w j = z)
        ≤ ∑ _j ∈ Finset.Ico m m', (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => prb_le_one hd0 hβ N _
      _ = ((Finset.Ico m m').card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hcard
  -- the tail of the window
  have hsplit : (∑ j ∈ Finset.Ico m m', prb N β (fun w => pos w j = z))
      + (∑ j ∈ Finset.Ico m' (m + h), prb N β (fun w => pos w j = z))
      = ∑ j ∈ Finset.Ico m (m + h), prb N β (fun w => pos w j = z) :=
    Finset.sum_Ico_consecutive _ hmm' hm'h
  -- step 1: the compensator, summed
  have hAB : ∑ j ∈ Finset.Ico m' (m + h), ∑ w : Fin N → Dir d, prob β w * Bterm β R z w j
      = ∑ j ∈ Finset.Ico m' (m + h), ∑ w : Fin N → Dir d, prob β w * Aterm β R z w j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjN : j + 1 ≤ N := by
      have := (Finset.mem_Ico.mp hj).2
      omega
    exact (expect_Aterm_eq_Bterm hd0 hβ R z j hjN).symm
  -- step 2: the pointwise bound on the compensated sum
  have hA : ∑ j ∈ Finset.Ico m' (m + h), ∑ w : Fin N → Dir d, prob β w * Aterm β R z w j
      ≤ (2 + 3 * greenConst d) * (if d = 2 then Real.log ((R : ℝ) + 1) else 1)
        + (β - 1) * (4 * (d : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (R : ℝ)) := by
    rw [Finset.sum_comm]
    have hpt : ∀ w : Fin N → Dir d,
        ∑ j ∈ Finset.Ico m' (m + h), prob β w * Aterm β R z w j
          ≤ prob β w * ((2 + 3 * greenConst d) * (if d = 2 then Real.log ((R : ℝ) + 1) else 1)
            + (β - 1) * (4 * (d : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (R : ℝ))) := by
      intro w
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (prob_nonneg hd0 hβ w)
      rw [← hkeq]
      exact pointwise_Aterm_bound hd hβ z w m' k (by omega) hR
    refine le_trans (Finset.sum_le_sum fun w _ => hpt w) ?_
    rw [← Finset.sum_mul, sum_prob_eq_one hd0 hβ N, one_mul]
  -- step 3: the lower bound on each `Bterm`
  have hB : 2 * (∑ j ∈ Finset.Ico m' (m + h), prb N β (fun w => pos w j = z))
        - ((k : ℝ) * (4 * (d : ℝ) * (greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2))))
      ≤ ∑ j ∈ Finset.Ico m' (m + h), ∑ w : Fin N → Dir d, prob β w * Bterm β R z w j := by
    have hterm : ∀ j ∈ Finset.Ico m' (m + h),
        2 * prb N β (fun w => pos w j = z)
            - 4 * (d : ℝ) * (greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2))
          ≤ ∑ w : Fin N → Dir d, prob β w * Bterm β R z w j := by
      intro j hj
      have h1 : m' ≤ j := (Finset.mem_Ico.mp hj).1
      have h2 : j < m + h := (Finset.mem_Ico.mp hj).2
      exact two_prb_le hd hβ z (by omega) (by omega) hR
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hterm)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
      hk]
  -- assemble
  have hHnn : (0 : ℝ) ≤ (if d = 2 then Real.log ((R : ℝ) + 1) else 1) := by
    by_cases h2 : d = 2
    · rw [if_pos h2]
      have h1 : (1 : ℝ) ≤ (R : ℝ) + 1 := by
        have : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
        linarith
      have := Real.log_le_log (by norm_num) h1
      simpa using this
    · rw [if_neg h2]; norm_num
  have hrpow : (0 : ℝ) ≤ (R : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg R) _
  have hkh : (k : ℝ) ≤ (h : ℝ) := by
    have : k ≤ h := by omega
    exact_mod_cast this
  have hbeta : (0 : ℝ) ≤ β - 1 := by linarith
  have hocc := occConst_nonneg d
  have hocc1 : 2 * (d : ℝ) * greenConst d ≤ occConst d := by
    unfold occConst
    have h3 : (0 : ℝ) ≤ 2 * (d : ℝ) ^ ((3 : ℝ) / 2) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    linarith
  have hocc2 : (2 + 3 * greenConst d) / 2 ≤ occConst d := by
    unfold occConst
    have h1 : (0 : ℝ) ≤ 2 * (d : ℝ) * greenConst d := mul_nonneg (by positivity) hg
    have h3 : (0 : ℝ) ≤ 2 * (d : ℝ) ^ ((3 : ℝ) / 2) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    linarith
  have hocc3 : 2 * (d : ℝ) ^ ((3 : ℝ) / 2) ≤ occConst d := by
    unfold occConst
    have h1 : (0 : ℝ) ≤ 2 * (d : ℝ) * greenConst d := mul_nonneg (by positivity) hg
    linarith
  have hkey : 2 * (∑ j ∈ Finset.Ico m' (m + h), prb N β (fun w => pos w j = z))
      ≤ (2 + 3 * greenConst d) * (if d = 2 then Real.log ((R : ℝ) + 1) else 1)
        + (β - 1) * (4 * (d : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (R : ℝ))
        + (h : ℝ) * (4 * (d : ℝ) * (greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2))) := by
    have hmono : (k : ℝ) * (4 * (d : ℝ) * (greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2)))
        ≤ (h : ℝ) * (4 * (d : ℝ) * (greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2))) := by
      refine mul_le_mul_of_nonneg_right hkh ?_
      have : (0 : ℝ) ≤ greenConst d * (R : ℝ) ^ (-(d : ℝ) / 2) := mul_nonneg hg hrpow
      nlinarith
    linarith [hB, hAB.le, hAB.ge, hA]
  have hsqrt : (0 : ℝ) ≤ Real.sqrt (R : ℝ) := Real.sqrt_nonneg _
  have hhnn : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
  have hfinal : ∑ j ∈ Finset.Ico m' (m + h), prb N β (fun w => pos w j = z)
      ≤ occConst d * ((h : ℝ) * (R : ℝ) ^ (-(d : ℝ) / 2)
          + (if d = 2 then Real.log ((R : ℝ) + 1) else 1)
          + (β - 1) * Real.sqrt (R : ℝ)) := by
    have e1 : 2 * (d : ℝ) * greenConst d * ((h : ℝ) * (R : ℝ) ^ (-(d : ℝ) / 2))
        ≤ occConst d * ((h : ℝ) * (R : ℝ) ^ (-(d : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right hocc1 (mul_nonneg hhnn hrpow)
    have e2 : (2 + 3 * greenConst d) / 2 * (if d = 2 then Real.log ((R : ℝ) + 1) else 1)
        ≤ occConst d * (if d = 2 then Real.log ((R : ℝ) + 1) else 1) :=
      mul_le_mul_of_nonneg_right hocc2 hHnn
    have e3 : 2 * (d : ℝ) ^ ((3 : ℝ) / 2) * ((β - 1) * Real.sqrt (R : ℝ))
        ≤ occConst d * ((β - 1) * Real.sqrt (R : ℝ)) :=
      mul_le_mul_of_nonneg_right hocc3 (mul_nonneg hbeta hsqrt)
    nlinarith [hkey, e1, e2, e3]
  linarith [hsplit, hhead, hfinal]

/-! ### The trivial bound, and the two simplifications of `orrw.tex` -/

/-- Gives the trivial bound on the occupation count when the dimension is positive, the degenerate case where the walk's range cannot fill space and the resistance estimates hold vacuously. -/
lemma occupation_trivial (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) (z : Site d) (m h : ℕ) {N : ℕ} :
    ∑ j ∈ Finset.Ico m (m + h), prb N β (fun w => pos w j = z) ≤ (h : ℝ) := by
  calc ∑ j ∈ Finset.Ico m (m + h), prb N β (fun w => pos w j = z)
      ≤ ∑ _j ∈ Finset.Ico m (m + h), (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => prb_le_one hd hβ N _
    _ = ((Finset.Ico m (m + h)).card : ℝ) := by simp
    _ = (h : ℝ) := by rw [Nat.card_Ico]; simp

/-- `log y ≤ y^α / α` for `α > 0`. -/
lemma log_le_rpow {α y : ℝ} (hα : 0 < α) (hy : 0 < y) : Real.log y ≤ y ^ α / α := by
  have h1 : Real.log (y ^ α) ≤ y ^ α - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy α)
  rw [Real.log_rpow hy] at h1
  rw [le_div_iff₀ hα]
  nlinarith [Real.rpow_pos_of_pos hy α]

/-- `log(h+2) ≤ C h^{1/(d+1)}` (`orrw.tex`). -/
lemma H_le_rpow (d : ℕ) (hd : 2 ≤ d) {N : ℕ} (hN : 1 ≤ N) :
    (if d = 2 then Real.log ((N : ℝ) + 2) else 1) ≤ 6 * (N : ℝ) ^ (1 / ((d : ℝ) + 1)) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  by_cases h2 : d = 2
  · subst h2
    rw [if_pos rfl]
    have he : (1 : ℝ) / (((2 : ℕ) : ℝ) + 1) = 1 / 3 := by norm_num
    rw [he]
    have hy : (0 : ℝ) < (N : ℝ) + 2 := by linarith
    have h1 : Real.log ((N : ℝ) + 2) ≤ ((N : ℝ) + 2) ^ ((1 : ℝ) / 3) / (1 / 3) :=
      log_le_rpow (by norm_num) hy
    have h2' : ((N : ℝ) + 2) ^ ((1 : ℝ) / 3) ≤ (3 * (N : ℝ)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have h3 : (3 * (N : ℝ)) ^ ((1 : ℝ) / 3)
        = (3 : ℝ) ^ ((1 : ℝ) / 3) * (N : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have h4 : (3 : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 := by
      have e8 : (8 : ℝ) ^ ((1 : ℝ) / 3) = 2 := by
        rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]; norm_num,
          ← Real.rpow_mul (by norm_num)]
        norm_num
      calc (3 : ℝ) ^ ((1 : ℝ) / 3) ≤ (8 : ℝ) ^ ((1 : ℝ) / 3) :=
            Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        _ = 2 := e8
    have hnn : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
    nlinarith [h1, h2', h3, h4, hnn]
  · rw [if_neg h2]
    have hexp : (0 : ℝ) ≤ 1 / ((d : ℝ) + 1) := by positivity
    have : (1 : ℝ) ≤ (N : ℝ) ^ (1 / ((d : ℝ) + 1)) := Real.one_le_rpow hN1 hexp
    linarith

/-- `(β-1)^{d/(d+1)} ≤ β` (`orrw.tex`). -/
lemma rpow_sub_one_le (d : ℕ) {β : ℝ} (hβ : 1 ≤ β) :
    (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) ≤ β := by
  have ht : (0 : ℝ) ≤ β - 1 := by linarith
  have hθ0 : (0 : ℝ) ≤ (d : ℝ) / ((d : ℝ) + 1) := by positivity
  have hθ1 : (d : ℝ) / ((d : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  by_cases hc : β - 1 ≤ 1
  · have := Real.rpow_le_one ht hc hθ0
    linarith
  · push_neg at hc
    have h1 : (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) ≤ (β - 1) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hc) hθ1
    rw [Real.rpow_one] at h1
    linarith

end ORRW
