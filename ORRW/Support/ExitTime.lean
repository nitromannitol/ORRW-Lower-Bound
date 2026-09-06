/-
Supporting lemmas for the exit time bounds of Bou-Rabee--Peres, Section 2,
`orrw.tex` (label `lem:max-exit`).

Nothing here is frozen.  `ORRW/Support/BoxAverage.lean` proves the third
assertion `T(A) ≤ C|A|^{1+2/d}`; this file deduces the other two from it and
assembles the three into the form the frozen statement asks for.

The step from the total mass to the maximum is the level set induction of
Grigor'yan and Telcs, carried out on the cardinality of `A`:

* `u_le_level`.  For `t ≥ 0` let `A_t := {x ∈ A : u_A(x) > t}`.  Then
  `u_A ≤ t + u_{A_t}` everywhere.  Off `A_t` this is the definition of `A_t`
  together with `u_{A_t} ≥ 0`; on `A_t` it is the maximum principle applied to
  `u_A - t - u_{A_t}`, whose zero extension dominates `u_A - t - u_{A_t}`
  pointwise precisely because `u_A ≤ t` off `A_t`, and whose Laplacian is
  therefore nonnegative, the two constants `-1` cancelling.

* `u_bound`.  Take `t := 2C₀|A|^{2/d}`, twice the average value of `u_A`
  measured against the total mass bound.  Chebyshev gives `|A_t| ≤ |A|/2`, so
  induction on the cardinality applies to `A_t`, and
  `‖u_A‖_∞ ≤ t + ‖u_{A_t}‖_∞ ≤ (2C₀ + K2^{-2/d})|A|^{2/d}`.  The constant
  `K := 2C₀/(1 - 2^{-2/d})` is exactly the one that makes this at most
  `K|A|^{2/d}`, and it is finite for every `d ≥ 1`.

* `h_bound`.  `h_A(x) = 1 + ∑_{y ∈ A, y ∼ x} u_A(y)` has at most `2d` terms.
-/
import Mathlib
import ORRW.Basic
import ORRW.Lattice
import ORRW.Support.Insertion
import ORRW.Support.Thomson
import ORRW.Support.BoxAverage

open Finset
open scoped Matrix

namespace ORRW.Support

variable {d : ℕ}

/-! ## The level set comparison -/

/-- `u_A ≤ t + u_{A_t}`, where `A_t` is the set on which `u_A` exceeds `t`. -/
lemma u_le_level (hd : 0 < d) (A : Finset (Site d)) {t : ℝ} (ht : 0 ≤ t) (y : Site d) :
    u A y ≤ t + u (A.filter (fun z => t < u A z)) y := by
  classical
  set B := A.filter (fun z => t < u A z) with hB
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have hout : ∀ z : Site d, z ∉ B → u A z ≤ t := by
    intro z hz
    by_cases hzA : z ∈ A
    · by_contra hcon
      push_neg at hcon
      exact hz (Finset.mem_filter.mpr ⟨hzA, hcon⟩)
    · rw [u_off A hzA]; exact ht
  by_cases hy : y ∈ B
  · set v : B → ℝ := fun w => u A (w : Site d) - t - u B (w : Site d) with hv
    have hkey : ∀ z : Site d, u A z - t - u B z ≤ extendZero B v z := by
      intro z
      by_cases hz : z ∈ B
      · have hc : extendZero B v z = v ⟨z, hz⟩ := extendZero_coe B v ⟨z, hz⟩
        rw [hc]
      · rw [extendZero_of_notMem B v hz, u_off B hz]
        have := hout z hz
        linarith
    have hsub : ∀ z : B, 0 ≤ (dirichletLaplacian B *ᵥ v) z := by
      intro z
      rw [dirichletLaplacian_mulVec_apply B v z]
      have h1 : ∑ a : Dir d, (u A ((z : Site d) + dirVec a) - t - u B ((z : Site d) + dirVec a))
          ≤ ∑ a : Dir d, extendZero B v ((z : Site d) + dirVec a) :=
        Finset.sum_le_sum fun a _ => hkey _
      have hA' := u_lap hd A (z : Site d) (hBA z.2)
      have hB' := u_lap hd B (z : Site d) z.2
      have hcard : ∑ _a : Dir d, t = 2 * (d:ℝ) * t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring
      have hexp : ∑ a : Dir d, (u A ((z : Site d) + dirVec a) - t - u B ((z : Site d) + dirVec a))
          = (∑ a : Dir d, u A ((z : Site d) + dirVec a)) - (∑ _a : Dir d, t)
            - ∑ a : Dir d, u B ((z : Site d) + dirVec a) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      rw [hexp, hA', hB', hcard] at h1
      have hvz : v z = u A (z : Site d) - t - u B (z : Site d) := rfl
      rw [hvz]
      linarith
    have hmp := maximum_principle hd B v hsub ⟨y, hy⟩
    have hvy : v ⟨y, hy⟩ = u A y - t - u B y := rfl
    rw [hvy] at hmp
    linarith
  · rw [u_off B hy]
    have := hout y hy
    linarith

/-! ## The maximum of the mean exit time -/

/-- `max_{x} u_A(x) ≤ C|A|^{2/d}`, the first assertion of `lem:max-exit`. -/
theorem u_bound (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (Site d)) (x : Site d),
      u A x ≤ C * (A.card : ℝ) ^ ((2:ℝ) / (d:ℝ)) := by
  classical
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hexp : (0:ℝ) < (2:ℝ) / (d:ℝ) := by positivity
  obtain ⟨C₀, hC₀pos, hC₀⟩ := T_bound hd
  set ρ : ℝ := (1/2 : ℝ) ^ ((2:ℝ) / (d:ℝ)) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρlt : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hexp
  set K : ℝ := 2 * C₀ / (1 - ρ) with hK
  have hKpos : 0 < K := by
    rw [hK]
    exact div_pos (by linarith) (by linarith)
  have hKC : 2 * C₀ ≤ K := by
    rw [hK, le_div_iff₀ (by linarith)]
    nlinarith [hC₀pos, hρpos]
  have hne : (1:ℝ) - ρ ≠ 0 := by linarith
  have hKmul : K * (1 - ρ) = 2 * C₀ := by
    rw [hK]
    field_simp
  have hKeq : 2 * C₀ + K * ρ = K := by linear_combination -hKmul
  refine ⟨K, hKpos, ?_⟩
  suffices H : ∀ n : ℕ, ∀ A : Finset (Site d), A.card = n → ∀ x : Site d,
      u A x ≤ K * (n : ℝ) ^ ((2:ℝ) / (d:ℝ)) by
    intro A x
    exact H A.card A rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hcard x
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0
      have hA : A = ∅ := Finset.card_eq_zero.mp hcard
      have hx : x ∉ A := by rw [hA]; exact Finset.notMem_empty x
      rw [u_off A hx, Nat.cast_zero, Real.zero_rpow (ne_of_gt hexp)]
      norm_num
    · have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
      set P : ℝ := (n : ℝ) ^ ((2:ℝ) / (d:ℝ)) with hP
      have hPpos : 0 < P := Real.rpow_pos_of_pos hnR _
      set t : ℝ := 2 * C₀ * P with ht
      have htpos : 0 < t := by rw [ht]; positivity
      set B : Finset (Site d) := A.filter (fun z => t < u A z) with hB
      have hTle : T A ≤ (t / 2) * (n:ℝ) := by
        have h1 := hC₀ A
        rw [hcard] at h1
        have h2 : (n:ℝ) ^ (1 + (2:ℝ)/(d:ℝ)) = (n:ℝ) * P := by
          rw [hP, Real.rpow_add hnR, Real.rpow_one]
        rw [h2] at h1
        rw [ht]
        linarith
      have hsum : (B.card : ℝ) * t ≤ T A := by
        have h1 : B.card • t ≤ ∑ z ∈ B, u A z := by
          refine Finset.card_nsmul_le_sum B (u A) t ?_
          intro z hz
          exact le_of_lt (Finset.mem_filter.mp hz).2
        rw [nsmul_eq_mul] at h1
        exact le_trans h1 (sum_u_le_T hd A B)
      have hhalf : 2 * (B.card : ℝ) ≤ (n:ℝ) := by
        have hle : (B.card : ℝ) * t ≤ (t/2) * (n:ℝ) := le_trans hsum hTle
        nlinarith [htpos]
      have hhalfN : 2 * B.card ≤ n := by exact_mod_cast hhalf
      rcases Finset.eq_empty_or_nonempty B with hBe | hBne
      · have hle : u A x ≤ t := by
          by_cases hxA : x ∈ A
          · by_contra hcon
            push_neg at hcon
            have hmem : x ∈ B := Finset.mem_filter.mpr ⟨hxA, hcon⟩
            rw [hBe] at hmem
            exact Finset.notMem_empty x hmem
          · rw [u_off A hxA]; exact le_of_lt htpos
        calc u A x ≤ t := hle
          _ = 2 * C₀ * P := ht
          _ ≤ K * P := by nlinarith [hPpos, hKC]
      · obtain ⟨y₀, hy₀⟩ := hBne
        have hBpos : 1 ≤ B.card := Finset.card_pos.mpr ⟨y₀, hy₀⟩
        have hBlt : B.card < n := by omega
        have hIH := ih B.card hBlt B rfl x
        have hBP : (B.card : ℝ) ^ ((2:ℝ)/(d:ℝ)) ≤ ρ * P := by
          have h1 : (B.card : ℝ) ≤ (n:ℝ) * (1/2 : ℝ) := by linarith
          have h2 : (B.card : ℝ) ^ ((2:ℝ)/(d:ℝ)) ≤ ((n:ℝ) * (1/2:ℝ)) ^ ((2:ℝ)/(d:ℝ)) :=
            Real.rpow_le_rpow (by positivity) h1 (le_of_lt hexp)
          rw [Real.mul_rpow (le_of_lt hnR) (by norm_num)] at h2
          rw [hP, hρ]
          linarith [h2]
        have hstep := u_le_level hd A (le_of_lt htpos) x
        rw [← hB] at hstep
        have hIH' : u B x ≤ K * (ρ * P) :=
          le_trans hIH (mul_le_mul_of_nonneg_left hBP (le_of_lt hKpos))
        calc u A x ≤ t + u B x := hstep
          _ ≤ 2 * C₀ * P + K * (ρ * P) := by rw [ht] at *; linarith
          _ = (2 * C₀ + K * ρ) * P := by ring
          _ = K * P := by rw [hKeq]

/-! ## The bound on `h` -/

/-- A site has at most `2d` neighbours. -/
lemma card_adj_le (A : Finset (Site d)) (x : Site d) :
    (A.filter (fun y => Adj y x)).card ≤ 2 * d := by
  classical
  have hsub : A.filter (fun y => Adj y x)
      ⊆ (Finset.univ : Finset (Dir d)).image (fun a => x - dirVec a) := by
    intro y hy
    obtain ⟨_, a, ha⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
    rw [ha]
    abel
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Dir d)))
    (f := fun a => x - dirVec a)
  have h3 : (Finset.univ : Finset (Dir d)).card = 2 * d := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    ring
  omega

/-! ## The three assertions of `lem:max-exit` -/

/-- Assembles the three exit time bounds for a finite set of sites into the frozen form of the maximum exit time lemma, deducing the uniform potential bound and the outside hitting estimate from the box average result via the level set induction. -/
theorem exit_time_bounds (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Finset (Site d), A.Nonempty →
      (∀ x ∈ A, u A x ≤ C * (A.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ∧
      (∀ x ∉ A, ORRW.h A x ≤ C * (A.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ∧
      T A ≤ C * (A.card : ℝ) ^ (1 + (2 : ℝ) / (d : ℝ)) := by
  classical
  have hd0 : 0 < d := hd
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hexp : (0:ℝ) ≤ (2:ℝ) / (d:ℝ) := by positivity
  obtain ⟨C₁, hC₁pos, hC₁⟩ := u_bound hd0
  obtain ⟨C₀, hC₀pos, hC₀⟩ := T_bound hd0
  refine ⟨max (1 + 2 * (d:ℝ) * C₁) C₀, ?_, ?_⟩
  · exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  intro A hA
  obtain ⟨x₀, hx₀⟩ := hA
  have hm1 : 1 ≤ A.card := Finset.card_pos.mpr ⟨x₀, hx₀⟩
  have hmR : (1:ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hm1
  set P : ℝ := (A.card : ℝ) ^ ((2:ℝ) / (d:ℝ)) with hP
  have hP1 : (1:ℝ) ≤ P := Real.one_le_rpow hmR hexp
  have hPnn : (0:ℝ) ≤ P := by linarith
  have hC₁le : C₁ ≤ max (1 + 2 * (d:ℝ) * C₁) C₀ :=
    le_trans (by nlinarith [hC₁pos, hdR]) (le_max_left _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro x _
    exact le_trans (hC₁ A x) (mul_le_mul_of_nonneg_right hC₁le hPnn)
  · intro x _
    have hb : ∑ y ∈ A.filter (fun y => Adj y x), u A y
        ≤ (A.filter (fun y => Adj y x)).card • (C₁ * P) :=
      Finset.sum_le_card_nsmul _ _ _ (fun y _ => hC₁ A y)
    rw [nsmul_eq_mul] at hb
    have hcnt : ((A.filter (fun y => Adj y x)).card : ℝ) ≤ 2 * (d:ℝ) := by
      have := card_adj_le A x
      exact_mod_cast this
    have hb2 : ∑ y ∈ A.filter (fun y => Adj y x), u A y ≤ 2 * (d:ℝ) * (C₁ * P) := by
      refine le_trans hb ?_
      exact mul_le_mul_of_nonneg_right hcnt (by positivity)
    have hstep : ORRW.h A x ≤ 1 + 2 * (d:ℝ) * (C₁ * P) := by
      rw [ORRW.h]
      linarith
    refine le_trans hstep ?_
    have h1 : (1:ℝ) + 2 * (d:ℝ) * (C₁ * P) ≤ (1 + 2 * (d:ℝ) * C₁) * P := by nlinarith [hP1]
    refine le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) hPnn)
  · refine le_trans (hC₀ A) (mul_le_mul_of_nonneg_right (le_max_right _ _) ?_)
    positivity

end ORRW.Support
