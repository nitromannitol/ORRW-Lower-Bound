/-
Supporting lemmas for Proposition 3.3 of Bou-Rabee--Peres (`prop:charge`,
`orrw.tex`): the charge accumulated by the time the walk has crossed `k`
distinct edges is at most `Kβk^{1+1/d}`.

Nothing here is frozen.  The parts are

* domain monotonicity of `u` and `h`, the analytic input the paper calls on
  twice in the proof (`orrw.tex`);

* the charge as a sum over `j = 1, …, |E_m|`, which is `orrw.tex`: the
  steps at which `η = 1` are exactly `σ_1, …, σ_{|E_m|}`, and
  `S_{σ_j-1} = S_{σ_{j-1}}` because no new edge is crossed in between;

* the multiplicity bound of `orrw.tex` ("A site occurs as `v_j` for at
  most `2d` indices `j`, because those indices carry distinct edges incident to
  it");

* the assembly with `lem:walk-order` and `lem:insertion`.
-/
import ORRW.Support.WalkOrder
import ORRW.Support.InsertionSum

namespace ORRW.Support

open Finset ORRW
open scoped Matrix

variable {d n : ℕ}

/-! ### Domain monotonicity -/

/-- A domain monotonicity fact giving the lower bound on the potential at a site, used twice in the proof of the charge estimate. -/
lemma u_lap_ge (hd : 0 < d) (A : Finset (Site d)) (y : Site d) :
    -1 ≤ (∑ a : Dir d, u A (y + dirVec a)) - 2 * (d : ℝ) * u A y := by
  by_cases hy : y ∈ A
  · rw [u_lap hd A y hy]
    linarith
  · rw [u_eq_zero_of_notMem A hy]
    have h : (0 : ℝ) ≤ ∑ a : Dir d, u A (y + dirVec a) :=
      Finset.sum_nonneg fun a _ => u_nonneg hd A _
    linarith

/-- Provides the domain monotonicity step showing the difference of potentials, extended by zero, is nonnegative when enlarging the finite set, the analytic input used twice in the charge bound. -/
lemma extendZero_u_sub (A B : Finset (Site d)) (hAB : A ⊆ B) :
    extendZero B (fun z : B => u A (z : Site d) - u B (z : Site d))
      = fun y => u A y - u B y := by
  funext y
  by_cases hy : y ∈ B
  · simp [extendZero, hy]
  · rw [extendZero_of_notMem B _ hy, u_eq_zero_of_notMem A (fun hc => hy (hAB hc)),
      u_eq_zero_of_notMem B hy]
    ring

/-- Domain monotonicity of the mean exit time: a larger set takes longer to leave. -/
lemma u_mono (hd : 0 < d) {A B : Finset (Site d)} (hAB : A ⊆ B) (y : Site d) :
    u A y ≤ u B y := by
  by_cases hyB : y ∈ B
  · have hsub : ∀ z : B,
        0 ≤ (dirichletLaplacian B *ᵥ (fun z : B => u A (z : Site d) - u B (z : Site d))) z := by
      intro z
      rw [dirichletLaplacian_mulVec_apply, extendZero_u_sub A B hAB]
      have hsplit : (∑ a : Dir d, (u A ((z : Site d) + dirVec a) - u B ((z : Site d) + dirVec a)))
          = (∑ a : Dir d, u A ((z : Site d) + dirVec a))
            - ∑ a : Dir d, u B ((z : Site d) + dirVec a) :=
        Finset.sum_sub_distrib _ _
      rw [hsplit]
      have hB := u_lap hd B (z : Site d) z.2
      have hA := u_lap_ge hd A (z : Site d)
      linarith
    have hle := maximum_principle hd B (fun z : B => u A (z : Site d) - u B (z : Site d))
      hsub ⟨y, hyB⟩
    have hle' : u A y - u B y ≤ 0 := hle
    linarith
  · have h1 : y ∉ A := fun hc => hyB (hAB hc)
    rw [u_eq_zero_of_notMem A h1, u_eq_zero_of_notMem B hyB]

/-- Domain monotonicity of `h`. -/
lemma h_mono (hd : 0 < d) {A B : Finset (Site d)} (hAB : A ⊆ B) (x : Site d) :
    ORRW.h A x ≤ ORRW.h B x := by
  have h1 := sum_u_nbr A x
  have h2 := sum_u_nbr B x
  have h3 : ∑ a : Dir d, u A (x + dirVec a) ≤ ∑ a : Dir d, u B (x + dirVec a) :=
    Finset.sum_le_sum fun a _ => u_mono hd hAB _
  linarith


/-! ### The charge as a sum over the new-edge times -/

/-- Identifies the charge accumulated through time m as a sum over the crossed edges, reindexing the steps at which a new edge appears. -/
lemma Gamma_eq_sum (β : ℝ) (w : Fin n → Dir d) (m : ℕ) :
    Gamma β w m = ∑ t ∈ Finset.range m, eta w (t + 1) * (gamma β w t + Phi w (t + 1)) := by
  induction m with
  | zero => simp [Gamma]
  | succ m ih =>
    rw [show Gamma β w (m + 1)
        = Gamma β w m + eta w (m + 1) * (gamma β w m + Phi w (m + 1)) from rfl, ih,
      Finset.sum_range_succ]

/-- At the step immediately following the crossing of a new edge, the walk's range gains exactly that edge, tying the indicator η to the enumeration of distinct edges crossed. -/
lemma eta_succ_eq (w : Fin n → Dir d) (t : ℕ) :
    eta w (t + 1) = if (E w t).card < (E w (t + 1)).card then 1 else 0 := by
  unfold eta
  simp only [Nat.add_sub_cancel]

/-- The set of edges crossed by the walk up to time m cannot exceed those crossed by the horizon time n, the monotonicity used when bounding the charge over the crossing times. -/
lemma card_E_le_horizon (w : Fin n → Dir d) (m : ℕ) : (E w m).card ≤ (E w n).card := by
  rcases le_total m n with h | h
  · exact card_E_mono w h
  · have he : E w m = E w n := by unfold E; rw [Nat.min_eq_right h, Nat.min_self]
    rw [he]

/-- Bounds the exit time of the walk from the range of the first m edges by the number of distinct edges crossed, so that the charge accumulated up to the j-th new edge can be indexed against the edge set. -/
lemma sigma_le_of_le_card (w : Fin n → Dir d) {j m : ℕ} (hj : j ≤ (E w m).card) :
    sigma w j ≤ m := by
  rcases le_total m n with h | h
  · exact (sigma_le_iff w h).mpr hj
  · exact le_trans (sigma_le_horizon w (le_trans hj (card_E_le_horizon w m))) h

/-- The sites visited just before each of the first k distinct-edge crossing times are pairwise distinct, so that the charge sum can be indexed by edges without multiplicity. -/
lemma sigma_pred_injOn (w : Fin n → Dir d) {k : ℕ} (hfin : k ≤ (E w n).card) :
    Set.InjOn (fun j => sigma w j - 1) ((Finset.Icc 1 k : Finset ℕ) : Set ℕ) := by
  intro j₁ h₁ j₂ h₂ heq
  simp only [Finset.coe_Icc, Set.mem_Icc] at h₁ h₂
  simp only at heq
  have hs₁ : 1 ≤ sigma w j₁ := sigma_pos w h₁.1
  have hs₂ : 1 ≤ sigma w j₂ := sigma_pos w h₂.1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := sigma_strict_mono w hlt (le_trans h₂.2 hfin)
    omega
  · have := sigma_strict_mono w hlt (le_trans h₁.2 hfin)
    omega

/-- The steps at which a new edge is crossed are exactly `σ_1, …, σ_{|E_m|}`. -/
lemma new_edge_times (w : Fin n → Dir d) (m : ℕ) :
    (Finset.range m).filter (fun t => (E w t).card < (E w (t + 1)).card)
      = (Finset.Icc 1 (E w m).card).image (fun j => sigma w j - 1) := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨htm, hlt⟩
    have htn : t < n := by
      by_contra hc
      push_neg at hc
      rw [E_succ_eq_of_ge w hc] at hlt
      omega
    have hsig : sigma w (E w (t + 1)).card = t + 1 := by
      have hle : sigma w (E w (t + 1)).card ≤ t + 1 :=
        (sigma_le_iff w (by omega)).mpr (le_refl _)
      have hgt : ¬ (sigma w (E w (t + 1)).card ≤ t) := by
        intro hc
        have := (sigma_le_iff w (by omega)).mp hc
        omega
      omega
    refine ⟨(E w (t + 1)).card, ⟨by omega, card_E_mono w (by omega)⟩, ?_⟩
    simp only [hsig, Nat.add_sub_cancel]
  · rintro ⟨j, ⟨hj1, hjk⟩, rfl⟩
    have hjn : j ≤ (E w n).card := le_trans hjk (card_E_le_horizon w m)
    have hs1 : 1 ≤ sigma w j := sigma_pos w hj1
    have hsm : sigma w j ≤ m := sigma_le_of_le_card w hjk
    have hsn : sigma w j ≤ n := sigma_le_horizon w hjn
    have hc1 : (E w (sigma w j)).card = j := card_E_sigma w hjn
    have hc2 : (E w (sigma w j - 1)).card < j :=
      card_E_lt_of_lt_sigma w (by omega) (by omega)
    refine ⟨by omega, ?_⟩
    rw [show sigma w j - 1 + 1 = sigma w j by omega]
    omega

/-- Expresses the charge accumulated through time m as a sum over the crossed edges, one term per edge in the range. -/
lemma Gamma_eq_charge_sum (β : ℝ) (w : Fin n → Dir d) (m : ℕ) :
    Gamma β w m
      = ∑ j ∈ Finset.Icc 1 (E w m).card,
          (gamma β w (sigma w j - 1) + Phi w (sigma w j)) := by
  classical
  rw [Gamma_eq_sum]
  have h1 : ∀ t ∈ Finset.range m, eta w (t + 1) * (gamma β w t + Phi w (t + 1))
      = if (E w t).card < (E w (t + 1)).card then (gamma β w t + Phi w (t + 1)) else 0 := by
    intro t _
    rw [eta_succ_eq]
    split <;> ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, new_edge_times w m,
    Finset.sum_image (sigma_pred_injOn w (card_E_le_horizon w m))]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  rw [show sigma w j - 1 + 1 = sigma w j by have := sigma_pos w hj.1; omega]

/-- Identifies the site visited just before the walk crosses its j-th new edge, providing the indexing needed to enumerate the crossed edges in the charge bound. -/
lemma E_sigma_pred (w : Fin n → Dir d) {j : ℕ} (hj : 1 ≤ j) (hfin : j ≤ (E w n).card) :
    E w (sigma w j - 1) = E w (sigma w (j - 1)) := by
  have hjn1 : j - 1 ≤ (E w n).card := by omega
  have hs1 : 1 ≤ sigma w j := sigma_pos w hj
  have hlt : sigma w (j - 1) < sigma w j := sigma_strict_mono w (by omega) hfin
  have hsub : E w (sigma w (j - 1)) ⊆ E w (sigma w j - 1) := E_mono w (by omega)
  have hc1 : (E w (sigma w (j - 1))).card = j - 1 := card_E_sigma w hjn1
  have hc2 : (E w (sigma w j - 1)).card < j :=
    card_E_lt_of_lt_sigma w (by omega) (by have := sigma_le_horizon w hfin; omega)
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- The step count just before the j-th new edge crossing is positive, so the charge decomposition over the crossing times j = 1, …, |E_m| is well defined. -/
lemma nu_sigma_pred_ne_zero (hd : 0 < d) (w : Fin n → Dir d) {j : ℕ} (hj : 1 ≤ j)
    (hfin : j ≤ (E w n).card) : nu w (sigma w j - 1) ≠ 0 := by
  intro h0
  have hmem := (nu_eq_zero_iff hd w _).mp h0
  have hs1 : 1 ≤ sigma w j := sigma_pos w hj
  have hsn : sigma w j ≤ n := sigma_le_horizon w hfin
  have htn : sigma w j - 1 < n := by omega
  have hstep := ORRW.pos_succ w (sigma w j - 1) htn
  have hedge : edgeAt w (sigma w j - 1) ∈ E w (sigma w j - 1) := by
    have hm2 := (mem_S_iff hd w _ _).mp hmem (w ⟨sigma w j - 1, htn⟩)
    unfold edgeAt
    rw [hstep]
    exact hm2
  exact edge_new_at_sigma w hj hfin hedge


end ORRW.Support
