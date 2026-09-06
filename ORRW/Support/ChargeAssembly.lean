/-
Assembly of Proposition 3.3 of Bou-Rabee--Peres (`prop:charge`,
`orrw.tex`).

Nothing here is frozen.  `ORRW/Support/Charge.lean` supplies the decomposition
`Γ_m = ∑_{j=1}^{|E_m|} (γ_{σ_j-1} + Φ_{σ_j})` and the domain monotonicity of `u`
and `h`.  What is added here is

* `S` depends on the word only through the traversed-edge set, so that
  `S_{σ_j-1} = S_{σ_{j-1}}` (`orrw.tex`);

* the multiplicity bound of `orrw.tex` ("A site occurs as `v_j` for at
  most `2d` indices `j`, because those indices carry distinct edges incident to
  it"), together with the elementary counting lemma that turns a bound on the
  fibres of an index map into a bound on a sum;

* the assembly with `lem:walk-order` and `lem:insertion`.
-/
import ORRW.Support.Charge
import ORRW.Frozen.Potential.InsertionOrder
import ORRW.Frozen.Insertion.InsertionInequality

namespace ORRW.Support

open Finset ORRW

variable {d n : ℕ}

/-! ### Summing along an index map with bounded fibres -/

/-- If every fibre of `ι` over `s` has at most `c` elements and `F` is
nonnegative, then `∑_{j ∈ s} F(ι j) ≤ c ∑_i F i`. -/
lemma sum_comp_le_of_fiber_card_le {M : ℕ} (s : Finset ℕ) (ι : ℕ → Fin M) (F : Fin M → ℝ)
    (hF : ∀ i, 0 ≤ F i) (c : ℕ)
    (hc : ∀ i : Fin M, (s.filter (fun j => ι j = i)).card ≤ c) :
    ∑ j ∈ s, F (ι j) ≤ (c : ℝ) * ∑ i, F i := by
  classical
  have h1 : ∑ j ∈ s, F (ι j)
      = ∑ i : Fin M, ∑ j ∈ s.filter (fun j => ι j = i), F (ι j) :=
    (Finset.sum_fiberwise s ι (fun j => F (ι j))).symm
  rw [h1, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h2 : ∑ j ∈ s.filter (fun j => ι j = i), F (ι j)
      = ((s.filter (fun j => ι j = i)).card : ℝ) * F i := by
    rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]),
      Finset.sum_const, nsmul_eq_mul]
  rw [h2]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc i) (hF i)

/-! ### `S` depends on the word only through the traversed-edge set -/

/-- `orrw.tex`: no new edge is crossed between steps `σ_{j-1}` and
`σ_j - 1`, so `S_{σ_j-1} = S_{σ_{j-1}}`. -/
lemma S_sigma_pred (hd : 0 < d) (w : Fin n → Dir d) {j : ℕ} (hj : 1 ≤ j)
    (hfin : j ≤ (E w n).card) : S w (sigma w j - 1) = S w (sigma w (j - 1)) :=
  S_eq_of_E_eq hd w w (E_sigma_pred w hj hfin)

/-- The charge rate at the step before the `j`th discovery, in the form
`γ_{σ_j-1} = 2dβ h_{S_{σ_{j-1}}}(v_j)` of `orrw.tex`. -/
lemma gamma_sigma_pred_eq (hd : 0 < d) (β : ℝ) (w : Fin n → Dir d) {j : ℕ} (hj : 1 ≤ j)
    (hfin : j ≤ (E w n).card) :
    gamma β w (sigma w j - 1)
      = 2 * (d : ℝ) * β * ORRW.h (S w (sigma w (j - 1))) (pos w (sigma w j - 1)) := by
  unfold gamma
  rw [if_neg (nu_sigma_pred_ne_zero hd w hj hfin), S_sigma_pred hd w hj hfin]

/-! ### The multiplicity bound -/

/-- Distinct discoveries cross distinct edges. -/
lemma edgeAt_sigma_pred_ne (w : Fin n → Dir d) {k j₁ j₂ : ℕ} (h1 : 1 ≤ j₁) (hlt : j₁ < j₂)
    (h2k : j₂ ≤ k) (hfin : k ≤ (E w n).card) :
    edgeAt w (sigma w j₁ - 1) ≠ edgeAt w (sigma w j₂ - 1) := by
  have hf1 : j₁ ≤ (E w n).card := by omega
  have hf2 : j₂ ≤ (E w n).card := by omega
  have hs1 : 1 ≤ sigma w j₁ := sigma_pos w h1
  have hlts : sigma w j₁ < sigma w j₂ := sigma_strict_mono w hlt hf2
  have hn1 : sigma w j₁ ≤ n := sigma_le_horizon w hf1
  have hmem : edgeAt w (sigma w j₁ - 1) ∈ E w (sigma w j₁) :=
    edgeAt_mem_E w (by omega) (by omega)
  have hsub : E w (sigma w j₁) ⊆ E w (sigma w j₂ - 1) := E_mono w (by omega)
  intro hc
  exact edge_new_at_sigma w (by omega : 1 ≤ j₂) hf2 (hc ▸ hsub hmem)

/-- The edge crossed at step `σ_j` is incident to the departure site `v_j`. -/
lemma edgeAt_sigma_pred_eq (w : Fin n → Dir d) {j : ℕ} (hj : 1 ≤ j)
    (hfin : j ≤ (E w n).card) :
    ∃ a : Dir d, edgeAt w (sigma w j - 1)
      = s(pos w (sigma w j - 1), pos w (sigma w j - 1) + dirVec a) := by
  have hs1 : 1 ≤ sigma w j := sigma_pos w hj
  have hn : sigma w j ≤ n := sigma_le_horizon w hfin
  have htn : sigma w j - 1 < n := by omega
  refine ⟨w ⟨sigma w j - 1, htn⟩, ?_⟩
  rw [edgeAt, ORRW.pos_succ w (sigma w j - 1) htn]

/-- `orrw.tex`: a site occurs as `v_j` for at most `2d` indices `j`. -/
lemma departure_fiber_card_le (w : Fin n → Dir d) {k : ℕ}
    (hfin : k ≤ (E w n).card) (v : Site d) :
    (((Finset.Icc 1 k).filter (fun j => pos w (sigma w j - 1) = v)).card) ≤ 2 * d := by
  classical
  set s : Finset ℕ := (Finset.Icc 1 k).filter (fun j => pos w (sigma w j - 1) = v) with hs
  have hbounds : ∀ j ∈ s, 1 ≤ j ∧ j ≤ k ∧ pos w (sigma w j - 1) = v := by
    intro j hj
    rw [hs, Finset.mem_filter, Finset.mem_Icc] at hj
    exact ⟨hj.1.1, hj.1.2, hj.2⟩
  have hmaps : Set.MapsTo (fun j => edgeAt w (sigma w j - 1)) (s : Set ℕ)
      ((Finset.univ.image (fun a : Dir d => s(v, v + dirVec a))) : Set (Sym2 (Site d))) := by
    intro j hj
    obtain ⟨hj1, hjk, hjv⟩ := hbounds j hj
    obtain ⟨a, ha⟩ := edgeAt_sigma_pred_eq w hj1 (le_trans hjk hfin)
    have hmem : edgeAt w (sigma w j - 1)
        ∈ Finset.univ.image (fun b : Dir d => s(v, v + dirVec b)) := by
      rw [ha, hjv]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    exact Finset.mem_coe.mpr hmem
  have hinj : Set.InjOn (fun j => edgeAt w (sigma w j - 1)) (s : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ heq
    obtain ⟨h11, h1k, -⟩ := hbounds j₁ hj₁
    obtain ⟨h21, h2k, -⟩ := hbounds j₂ hj₂
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact edgeAt_sigma_pred_ne w h11 hlt h2k hfin heq
    · exact edgeAt_sigma_pred_ne w h21 hlt h1k hfin heq.symm
  refine le_trans (Finset.card_le_card_of_injOn _ hmaps hinj) ?_
  refine le_trans (Finset.card_image_le) ?_
  rw [card_dir]

/-! ### The charge sum along an insertion order

`orrw.tex`.  The departure terms are compared with `h_{A_{i-1}}(x_i)`,
each index `i` being used at most `2d` times, and the arrival terms with
`u_{A_i}(x_i)`, each index being used at most once. -/

set_option maxHeartbeats 1000000 in
/-- Upper-bounds the total charge accumulated by the walk by a resistance-weighted sum over the visited sites, using the fibre-multiplicity bound to control how often each site contributes. -/
lemma charge_sum_le (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) (w : Fin n → Dir d) {k : ℕ}
    (hfin : k ≤ (E w n).card)
    {M : ℕ} (hM1 : 1 ≤ M) (x : Fin M → Site d)
    (hximg : Finset.image x Finset.univ = R w (sigma w k))
    (hcl1 : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ i : Fin M,
        pos w (sigma w j - 1) = x i → S w (sigma w (j - 1)) ⊆ (Finset.Iio i).image x)
    (hcl2 : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ i : Fin M,
        pos w (sigma w j) ∈ S w (sigma w j) → pos w (sigma w j) = x i →
        S w (sigma w j) ⊆ insert (x i) ((Finset.Iio i).image x))
    (hcl3 : ∀ j₁ j₂ : ℕ, 1 ≤ j₁ → j₁ ≤ k → 1 ≤ j₂ → j₂ ≤ k →
        pos w (sigma w j₁) ∈ S w (sigma w j₁) → pos w (sigma w j₂) ∈ S w (sigma w j₂) →
        pos w (sigma w j₁) = pos w (sigma w j₂) → j₁ = j₂) :
    ∑ j ∈ Finset.Icc 1 k, (gamma β w (sigma w j - 1) + Phi w (sigma w j))
      ≤ 4 * (d : ℝ) ^ 2 * β * ∑ i : Fin M,
          (ORRW.h ((Finset.Iio i).image x) (x i)
            + u (insert (x i) ((Finset.Iio i).image x)) (x i)) := by
  classical
  haveI : Nonempty (Fin M) := ⟨⟨0, hM1⟩⟩
  have hβ0 : (0 : ℝ) ≤ β := le_trans zero_le_one hβ
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hFhnn : ∀ i : Fin M, (0 : ℝ) ≤ ORRW.h ((Finset.Iio i).image x) (x i) :=
    fun i => le_trans zero_le_one (one_le_h hd _ _)
  have hFunn : ∀ i : Fin M,
      (0 : ℝ) ≤ u (insert (x i) ((Finset.Iio i).image x)) (x i) :=
    fun i => u_nonneg hd _ _
  -- The index of the departure site `v_j` in the insertion order.
  have hvmem : ∀ j ∈ Finset.Icc 1 k, ∃ i : Fin M, x i = pos w (sigma w j - 1) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hs : sigma w j ≤ sigma w k := sigma_mono w hj.2 hfin
    have hmem : pos w (sigma w j - 1) ∈ R w (sigma w k) := ORRW.pos_mem_R w (by omega)
    rw [← hximg, Finset.mem_image] at hmem
    obtain ⟨i, _, hix⟩ := hmem
    exact ⟨i, hix⟩
  choose! iota hiota using hvmem
  -- The index of the arrival site `w_j`, when it is saturated.
  have hwmem : ∀ j ∈ (Finset.Icc 1 k).filter
      (fun j => pos w (sigma w j) ∈ S w (sigma w j)),
      ∃ i : Fin M, x i = pos w (sigma w j) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    have hs : sigma w j ≤ sigma w k := sigma_mono w hj.1.2 hfin
    have hmem : pos w (sigma w j) ∈ R w (sigma w k) := ORRW.pos_mem_R w hs
    rw [← hximg, Finset.mem_image] at hmem
    obtain ⟨i, _, hix⟩ := hmem
    exact ⟨i, hix⟩
  choose! kappa hkappa using hwmem
  -- Each index is a departure index at most `2d` times.
  have hfib1 : ∀ i : Fin M,
      ((Finset.Icc 1 k).filter (fun j => iota j = i)).card ≤ 2 * d := by
    intro i
    refine le_trans (Finset.card_le_card ?_) (departure_fiber_card_le w hfin (x i))
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨hj.1, ?_⟩
    rw [← hiota j hj.1, hj.2]
  -- Each index is an arrival index at most once.
  have hfib2 : ∀ i : Fin M,
      (((Finset.Icc 1 k).filter (fun j => pos w (sigma w j) ∈ S w (sigma w j))).filter
        (fun j => kappa j = i)).card ≤ 1 := by
    intro i
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    have hae : pos w (sigma w a) = pos w (sigma w b) := by
      rw [← hkappa a ha.1, ← hkappa b hb.1, ha.2, hb.2]
    have ha' := ha.1
    have hb' := hb.1
    rw [Finset.mem_filter, Finset.mem_Icc] at ha' hb'
    exact hcl3 a b ha'.1.1 ha'.1.2 hb'.1.1 hb'.1.2 ha'.2 hb'.2 hae
  -- The departure sum.
  have h2dβ : (0 : ℝ) ≤ 2 * (d : ℝ) * β := mul_nonneg (by positivity) hβ0
  have h2d : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  have hcast : ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) := by push_cast; ring
  have hgamsum : ∑ j ∈ Finset.Icc 1 k, gamma β w (sigma w j - 1)
      ≤ 4 * (d : ℝ) ^ 2 * β
          * ∑ i : Fin M, ORRW.h ((Finset.Iio i).image x) (x i) := by
    have step1 : ∑ j ∈ Finset.Icc 1 k, gamma β w (sigma w j - 1)
        ≤ ∑ j ∈ Finset.Icc 1 k,
            2 * (d : ℝ) * β * ORRW.h ((Finset.Iio (iota j)).image x) (x (iota j)) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' := Finset.mem_Icc.mp hj
      have hjfin : j ≤ (E w n).card := le_trans hj'.2 hfin
      rw [gamma_sigma_pred_eq hd β w hj'.1 hjfin, hiota j hj]
      exact mul_le_mul_of_nonneg_left
        (h_mono hd (hcl1 j hj'.1 hj'.2 (iota j) (hiota j hj).symm) _) h2dβ
    have step2 := sum_comp_le_of_fiber_card_le (Finset.Icc 1 k) iota
      (fun i : Fin M => ORRW.h ((Finset.Iio i).image x) (x i)) hFhnn (2 * d) hfib1
    rw [hcast] at step2
    have step3 : ∑ j ∈ Finset.Icc 1 k,
          2 * (d : ℝ) * β * ORRW.h ((Finset.Iio (iota j)).image x) (x (iota j))
        = 2 * (d : ℝ) * β
            * ∑ j ∈ Finset.Icc 1 k, ORRW.h ((Finset.Iio (iota j)).image x) (x (iota j)) :=
      (Finset.mul_sum _ _ _).symm
    have step4 := mul_le_mul_of_nonneg_left step2 h2dβ
    have hfinal : 2 * (d : ℝ) * β * (2 * (d : ℝ)
          * ∑ i : Fin M, ORRW.h ((Finset.Iio i).image x) (x i))
        = 4 * (d : ℝ) ^ 2 * β * ∑ i : Fin M, ORRW.h ((Finset.Iio i).image x) (x i) := by
      ring
    rw [step3] at step1
    rw [hfinal] at step4
    exact le_trans step1 step4
  -- The arrival sum.
  have hphisum : ∑ j ∈ Finset.Icc 1 k, Phi w (sigma w j)
      ≤ 2 * (d : ℝ)
          * ∑ i : Fin M, u (insert (x i) ((Finset.Iio i).image x)) (x i) := by
    have hrestrict : ∑ j ∈ (Finset.Icc 1 k).filter
          (fun j => pos w (sigma w j) ∈ S w (sigma w j)), Phi w (sigma w j)
        = ∑ j ∈ Finset.Icc 1 k, Phi w (sigma w j) := by
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro j hjm hjn
      rw [Finset.mem_filter] at hjn
      push_neg at hjn
      unfold Phi
      rw [u_eq_zero_of_notMem _ (hjn hjm)]
      ring
    have step1 : ∑ j ∈ (Finset.Icc 1 k).filter
          (fun j => pos w (sigma w j) ∈ S w (sigma w j)), Phi w (sigma w j)
        ≤ ∑ j ∈ (Finset.Icc 1 k).filter
            (fun j => pos w (sigma w j) ∈ S w (sigma w j)),
            2 * (d : ℝ) * u (insert (x (kappa j)) ((Finset.Iio (kappa j)).image x))
              (x (kappa j)) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' := hj
      rw [Finset.mem_filter, Finset.mem_Icc] at hj'
      unfold Phi
      rw [← hkappa j hj]
      exact mul_le_mul_of_nonneg_left
        (u_mono hd (hcl2 j hj'.1.1 hj'.1.2 (kappa j) hj'.2 (hkappa j hj).symm) _) h2d
    have step2 := sum_comp_le_of_fiber_card_le
      ((Finset.Icc 1 k).filter (fun j => pos w (sigma w j) ∈ S w (sigma w j))) kappa
      (fun i : Fin M => u (insert (x i) ((Finset.Iio i).image x)) (x i)) hFunn 1 hfib2
    have step3 : ∑ j ∈ (Finset.Icc 1 k).filter
          (fun j => pos w (sigma w j) ∈ S w (sigma w j)),
          2 * (d : ℝ) * u (insert (x (kappa j)) ((Finset.Iio (kappa j)).image x))
            (x (kappa j))
        = 2 * (d : ℝ) * ∑ j ∈ (Finset.Icc 1 k).filter
            (fun j => pos w (sigma w j) ∈ S w (sigma w j)),
            u (insert (x (kappa j)) ((Finset.Iio (kappa j)).image x)) (x (kappa j)) :=
      (Finset.mul_sum _ _ _).symm
    rw [Nat.cast_one, one_mul] at step2
    have step4 := mul_le_mul_of_nonneg_left step2 h2d
    rw [step3] at step1
    rw [hrestrict] at step1
    exact le_trans step1 step4
  -- Collect.
  have hSh : (0 : ℝ) ≤ ∑ i : Fin M, ORRW.h ((Finset.Iio i).image x) (x i) :=
    Finset.sum_nonneg fun i _ => hFhnn i
  have hSu : (0 : ℝ) ≤ ∑ i : Fin M, u (insert (x i) ((Finset.Iio i).image x)) (x i) :=
    Finset.sum_nonneg fun i _ => hFunn i
  have hcoef : 2 * (d : ℝ) ≤ 4 * (d : ℝ) ^ 2 * β := by nlinarith
  have hlast : 2 * (d : ℝ)
        * ∑ i : Fin M, u (insert (x i) ((Finset.Iio i).image x)) (x i)
      ≤ 4 * (d : ℝ) ^ 2 * β
        * ∑ i : Fin M, u (insert (x i) ((Finset.Iio i).image x)) (x i) :=
    mul_le_mul_of_nonneg_right hcoef hSu
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, mul_add]
  linarith [hgamsum, hphisum, hlast]

/-! ### Proposition 3.3 -/

set_option maxHeartbeats 1000000 in
/-- `orrw.tex` (`prop:charge`): `Γ_m ≤ Kβ|E_m|^{1+1/d}`. -/
theorem accumulated_charge_of {d : ℕ} (hd : 2 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 1 ≤ β → ∀ N : ℕ, ∀ w : Fin N → Dir d, ∀ m : ℕ,
      Gamma β w m ≤ K * β * ((E w m).card : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := ORRW.Frozen.insertion_inequality hd
  have hd1 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  refine ⟨16 * (d : ℝ) ^ 2 * C, by positivity, ?_⟩
  intro β hβ N w m
  have hβ0 : (0 : ℝ) ≤ β := le_trans zero_le_one hβ
  have hexp : (0 : ℝ) ≤ 1 + (1 : ℝ) / (d : ℝ) := by positivity
  have hfin : (E w m).card ≤ (E w N).card := card_E_le_horizon w m
  rcases Nat.eq_zero_or_pos (E w m).card with hk0 | hk1
  · -- `k = 0`: the sum is empty and the right-hand side vanishes.
    have hG : Gamma β w m = 0 := by
      rw [Gamma_eq_charge_sum, hk0]
      simp
    have hz : (((E w m).card : ℕ) : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) = 0 := by
      rw [hk0, Nat.cast_zero]
      exact Real.zero_rpow (by positivity)
    rw [hG, hz]
    simp
  · -- `k ≥ 1`.
    obtain ⟨hMle, x, hxinj, hximg, hcl1, hcl2, hcl3⟩ :=
      ORRW.Frozen.insertion_order (le_trans (by norm_num) hd) w (E w m).card hk1 hfin
    have hM1 : 1 ≤ (R w (sigma w (E w m).card)).card :=
      Finset.card_pos.mpr (R_nonempty w _)
    have hsum := charge_sum_le hd1 hβ w hfin hM1 x hximg hcl1 hcl2 hcl3
    have hins := hC _ hM1 x hxinj
    have hMk : ((R w (sigma w (E w m).card)).card : ℝ) ≤ 2 * ((E w m).card : ℝ) := by
      have h : (R w (sigma w (E w m).card)).card ≤ 2 * (E w m).card := by omega
      exact_mod_cast h
    have hQ : (0 : ℝ) ≤ ((E w m).card : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    have hPQ : ((R w (sigma w (E w m).card)).card : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ))
        ≤ 4 * ((E w m).card : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) := by
      have h1 : ((R w (sigma w (E w m).card)).card : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ))
          ≤ (2 * ((E w m).card : ℝ)) ^ (1 + (1 : ℝ) / (d : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hMk hexp
      have h2 : (2 * ((E w m).card : ℝ)) ^ (1 + (1 : ℝ) / (d : ℝ))
          = (2 : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ))
              * ((E w m).card : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) :=
        Real.mul_rpow (by norm_num) (by positivity)
      have h3 : (2 : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) ≤ 4 := by
        have hle : (1 : ℝ) + 1 / (d : ℝ) ≤ 2 := by
          have h1d : (1 : ℝ) / (d : ℝ) ≤ 1 := by
            rw [div_le_one (by linarith)]; linarith
          linarith
        have h2' := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hle
        have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
        linarith
      nlinarith [h1, h2, h3, hQ]
    have hcoef : (0 : ℝ) ≤ 4 * (d : ℝ) ^ 2 * β := by positivity
    have hstep1 := mul_le_mul_of_nonneg_left hins hcoef
    have hstep2 : C * ((R w (sigma w (E w m).card)).card : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ))
        ≤ C * (4 * ((E w m).card : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ))) :=
      mul_le_mul_of_nonneg_left hPQ hCpos.le
    have hstep3 := mul_le_mul_of_nonneg_left hstep2 hcoef
    have hstep4 : 4 * (d : ℝ) ^ 2 * β
          * (C * (4 * ((E w m).card : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ))))
        = 16 * (d : ℝ) ^ 2 * C * β * ((E w m).card : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) := by
      ring
    rw [Gamma_eq_charge_sum]
    calc ∑ j ∈ Finset.Icc 1 (E w m).card,
          (gamma β w (sigma w j - 1) + Phi w (sigma w j))
        ≤ 4 * (d : ℝ) ^ 2 * β * ∑ i : Fin (R w (sigma w (E w m).card)).card,
            (ORRW.h ((Finset.Iio i).image x) (x i)
              + u (insert (x i) ((Finset.Iio i).image x)) (x i)) := hsum
      _ ≤ 4 * (d : ℝ) ^ 2 * β
            * (C * ((R w (sigma w (E w m).card)).card : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ))) := hstep1
      _ ≤ 4 * (d : ℝ) ^ 2 * β
            * (C * (4 * ((E w m).card : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)))) := hstep3
      _ = 16 * (d : ℝ) ^ 2 * C * β
            * ((E w m).card : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) := hstep4

end ORRW.Support
