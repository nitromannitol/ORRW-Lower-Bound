/-
The electrical content of the one-point insertion lemma of Bou-Rabee--Peres, label `lem:schur`,
display `eq:schur` (orrw.tex:452-455):

  "Give every edge of `ℤ^d` unit conductance and let `Reff(x ↔ (A⁺)^c)` be the effective
   resistance between `x` and the grounded complement of `A⁺`.  Then
     `Reff(x ↔ (A⁺)^c) = -Δ_{A⁺}^{-1}(x,x) ≥ 1/(2d)`."

`LatticeProb.Reff A x` is the matrix entry `-Δ_{A⁺}^{-1}(x,x)` (convention L-002 of
`LatticeProb.Walk.Dirichlet`). This file defines the effective resistance of the electrical
network `ℤ^d` with unit conductances between `x` and the grounded set `(A⁺)^c` as in
Lyons--Peres, *Probability on Trees and Networks*, Section 2.2: the unit voltage is the function
harmonic at every vertex of `A⁺` other than `x`, equal to `1` at `x` and to `0` off `A⁺`, and the
effective resistance is the voltage drop `1` divided by the current that the unit voltage sends
out of `x`. It proves that the unit voltage exists and is unique, that this effective resistance
is `-Δ_{A⁺}^{-1}(x,x)`, and the Dirichlet principle: every voltage that is `1` at `x` and `0` off
`A⁺` has energy at least `1 / Reff`, with equality for the unit voltage.
-/
import ORRW.Basic
import LatticeProb.Walk.Dirichlet
import LatticeProb.Walk.Harmonic
import LatticeProb.Walk.Energy
import ORRW.Frozen.Insertion.OnePointInsertion

open LatticeProb Finset
open scoped Matrix

namespace ORRW.Electrical

variable {d : ℕ}

/-! ### The unit voltage and the effective resistance -/

/-- `v` is the unit voltage between `x` and the grounded complement of `A⁺ = insert x A`: it is
`1` at `x`, `0` off `A⁺`, and harmonic at every vertex of `A`. -/
def IsUnitVoltage (A : Finset (Site d)) (x : Site d) (v : Site d → ℝ) : Prop :=
  v x = 1 ∧ (∀ z, z ∉ insert x A → v z = 0) ∧
    ∀ y ∈ A, ∑ a : Dir d, v (y + dirVec a) = 2 * d * v y

/-- The current that the voltage `v` sends out of `x`, every edge having conductance one. -/
def currentOut (v : Site d → ℝ) (x : Site d) : ℝ :=
  ∑ a : Dir d, (v x - v (x + dirVec a))

open scoped Classical in
/-- The effective resistance between `x` and the grounded complement of `A⁺ = insert x A` in the
network `ℤ^d` with unit conductances: the voltage drop `1` of the unit voltage divided by the
current it sends out of `x`. It is `0` if there is no unit voltage, which does not happen for
`d ≥ 1` and `x ∉ A` (`exists_isUnitVoltage`). -/
noncomputable def effResistance (A : Finset (Site d)) (x : Site d) : ℝ :=
  if h : ∃ v, IsUnitVoltage A x v then 1 / currentOut h.choose x else 0

/-- The Green function of `A⁺` with pole at `x`, normalized to be `1` at `x`. -/
noncomputable def voltage (A : Finset (Site d)) (x : Site d) : Site d → ℝ :=
  fun z => green (insert x A) ⟨x, Finset.mem_insert_self x A⟩ z /
    green (insert x A) ⟨x, Finset.mem_insert_self x A⟩ x

theorem green_self (A : Finset (Site d)) (x : Site d) :
    green (insert x A) ⟨x, Finset.mem_insert_self x A⟩ x = -Reff A x := by
  rw [Reff_eq_neg_green, neg_neg]

theorem reff_pos (hd : 1 ≤ d) {A : Finset (Site d)} {x : Site d} (hx : x ∉ A) :
    0 < Reff A x := by
  obtain ⟨-, -, hR⟩ := LatticeProb.one_point_insertion hd A x hx
  have hdpos : (0 : ℝ) < 2 * (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  exact lt_of_lt_of_le (by positivity) hR

theorem card_dir : (Finset.univ : Finset (Dir d)).card = 2 * d := by
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-- **The unit voltage exists**: the Green function of `A⁺` with pole at `x`, normalized at `x`. -/
theorem isUnitVoltage_voltage (hd : 1 ≤ d) {A : Finset (Site d)} {x : Site d} (hx : x ∉ A) :
    IsUnitVoltage A x (voltage A x) := by
  have hg : green (insert x A) ⟨x, Finset.mem_insert_self x A⟩ x ≠ 0 := by
    rw [green_self]
    exact neg_ne_zero.mpr (reff_pos hd hx).ne'
  refine ⟨div_self hg, fun z hz => ?_, fun y hy => ?_⟩
  · simp only [voltage]
    rw [green, extendZero_of_notMem _ _ hz, zero_div]
  · have hyB : y ∈ insert x A := Finset.mem_insert_of_mem hy
    have hyx : y ≠ x := fun h => hx (h ▸ hy)
    have hlap := green_lap' (d := d) (by omega) (insert x A) ⟨x, Finset.mem_insert_self x A⟩ y hyB
    rw [if_neg hyx, add_zero] at hlap
    simp only [voltage]
    rw [← Finset.sum_div, hlap, mul_div_assoc]

theorem exists_isUnitVoltage (hd : 1 ≤ d) {A : Finset (Site d)} {x : Site d} (hx : x ∉ A) :
    ∃ v, IsUnitVoltage A x v :=
  ⟨voltage A x, isUnitVoltage_voltage hd hx⟩

/-- A function vanishing off a finite set `B` is the extension by zero of its restriction. -/
theorem extendZero_restrict (B : Finset (Site d)) {f : Site d → ℝ}
    (hf : ∀ z, z ∉ B → f z = 0) : extendZero B (fun z : B => f z) = f := by
  funext z
  by_cases hz : z ∈ B
  · exact extendZero_coe B (fun z : B => f z) ⟨z, hz⟩
  · rw [extendZero_of_notMem B _ hz, hf z hz]

/-- **The unit voltage is unique.** -/
theorem isUnitVoltage_unique (hd : 1 ≤ d) {A : Finset (Site d)} {x : Site d}
    {v w : Site d → ℝ} (hv : IsUnitVoltage A x v) (hw : IsUnitVoltage A x w) : v = w := by
  obtain ⟨hv1, hv0, hvh⟩ := hv
  obtain ⟨hw1, hw0, hwh⟩ := hw
  set δ : Site d → ℝ := fun z => v z - w z with hδ
  have hδ0 : ∀ z, z ∉ A → δ z = 0 := by
    intro z hz
    by_cases hzx : z = x
    · rw [hδ, hzx]
      simp only
      rw [hv1, hw1, sub_self]
    · have hzB : z ∉ insert x A := by
        rw [Finset.mem_insert]
        rintro (h | h)
        · exact hzx h
        · exact hz h
      rw [hδ]
      simp only
      rw [hv0 z hzB, hw0 z hzB, sub_self]
  have hext := extendZero_restrict A hδ0
  have hlap : ∀ y : A, (dirichletLaplacian A *ᵥ (fun z : A => δ z)) y = 0 := by
    intro y
    rw [dirichletLaplacian_mulVec_apply, hext]
    have h1 := hvh y y.2
    have h2 := hwh y y.2
    simp only [hδ, Finset.sum_sub_distrib]
    linarith
  have hle := maximum_principle (by omega) A (fun z : A => δ z) (fun y => (hlap y).ge)
  have hge := maximum_principle (by omega) A (fun z : A => -δ z) (fun y => by
    rw [show (fun z : A => -δ z) = -(fun z : A => δ z) from rfl, Matrix.mulVec_neg,
      Pi.neg_apply, hlap y, neg_zero])
  funext z
  by_cases hz : z ∈ A
  · have h1 := hle ⟨z, hz⟩
    have h2 := hge ⟨z, hz⟩
    simp only [hδ] at h1 h2
    linarith
  · have := hδ0 z hz
    simp only [hδ] at this
    linarith

/-- The current that the unit voltage sends out of `x` is `1 / Reff`. -/
theorem currentOut_voltage (hd : 1 ≤ d) {A : Finset (Site d)} {x : Site d} (hx : x ∉ A) :
    currentOut (voltage A x) x = 1 / Reff A x := by
  have hR := reff_pos hd hx
  have hlap := green_lap' (d := d) (by omega) (insert x A) ⟨x, Finset.mem_insert_self x A⟩ x
    (Finset.mem_insert_self x A)
  rw [if_pos rfl, green_self] at hlap
  have hsum : ∑ a : Dir d, voltage A x (x + dirVec a) = (2 * d * -Reff A x + 1) / -Reff A x := by
    simp only [voltage]
    rw [← Finset.sum_div, hlap, green_self]
  have hvx : voltage A x x = 1 := (isUnitVoltage_voltage hd hx).1
  have hR0 : Reff A x ≠ 0 := hR.ne'
  rw [currentOut, Finset.sum_sub_distrib, hsum, hvx, Finset.sum_const, card_dir, nsmul_eq_mul]
  field_simp
  push_cast
  ring

/-- **The first equality of `eq:schur`, electrically.** The effective resistance between `x` and
the grounded complement of `A⁺` is `-Δ_{A⁺}^{-1}(x,x)`. -/
theorem effResistance_eq_Reff (hd : 1 ≤ d) {A : Finset (Site d)} {x : Site d} (hx : x ∉ A) :
    effResistance A x = Reff A x := by
  have h := exists_isUnitVoltage hd hx
  rw [effResistance, dif_pos h,
    isUnitVoltage_unique hd h.choose_spec (isUnitVoltage_voltage hd hx),
    currentOut_voltage hd hx, one_div_one_div]

/-! ### The Dirichlet principle -/

/-- The sites of `B` together with their neighbours. -/
def siteNbhd (B : Finset (Site d)) : Finset (Site d) :=
  B ∪ B.biUnion fun y => (dirs d).image fun v => y + v

theorem subset_siteNbhd (B : Finset (Site d)) : B ⊆ siteNbhd B := Finset.subset_union_left

theorem add_mem_siteNbhd {B : Finset (Site d)} {z v : Site d} (hz : z ∈ B) (hv : v ∈ dirs d) :
    z + v ∈ siteNbhd B :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_image_of_mem _ hv⟩)

/-- The Dirichlet energy `∑_{{y,z}} (f y - f z)^2` of a function vanishing off the finite set `B`,
summed over the unit-conductance edges of `ℤ^d`. Every edge carrying a nonzero term has an end in
`B`, so it is counted twice in the directed energy over the sites of `B` and their neighbours. -/
noncomputable def edgeEnergy (B : Finset (Site d)) (f : Site d → ℝ) : ℝ :=
  energy (siteNbhd B) f / 2

/-- Summation by parts on a finite set: the lattice Laplacian is symmetric on functions vanishing
off `B`. -/
theorem sum_mul_sum_dir_symm (B : Finset (Site d)) {f g : Site d → ℝ}
    (hf : ∀ z, z ∉ B → f z = 0) (hg : ∀ z, z ∉ B → g z = 0) :
    ∑ y ∈ B, g y * ∑ a : Dir d, f (y + dirVec a) = ∑ y ∈ B, f y * ∑ a : Dir d, g (y + dirVec a) := by
  have key : ∀ f g : Site d → ℝ, (∀ z, z ∉ B → f z = 0) →
      ∑ y ∈ B, g y * ∑ a : Dir d, f (y + dirVec a)
        = (fun z : B => g z) ⬝ᵥ (dirichletLaplacian B *ᵥ (fun z : B => f z))
          + 2 * d * ∑ y ∈ B, g y * f y := by
    intro f g hf
    rw [dotProduct, Finset.mul_sum, ← Finset.sum_coe_sort B, ← Finset.sum_coe_sort B,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [dirichletLaplacian_mulVec_apply, extendZero_restrict B hf]
    ring
  have hsymm : (fun z : B => g z) ⬝ᵥ (dirichletLaplacian B *ᵥ (fun z : B => f z))
      = (fun z : B => f z) ⬝ᵥ (dirichletLaplacian B *ᵥ (fun z : B => g z)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dirichletLaplacian_transpose,
      dotProduct_comm]
  rw [key f g hf, key g f hg, hsymm]
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun y _ => mul_comm _ _

/-- The energy of a function vanishing off `B` as its pairing with the negative Laplacian. -/
theorem edgeEnergy_eq (B : Finset (Site d)) {f : Site d → ℝ} (hf : ∀ z, z ∉ B → f z = 0) :
    edgeEnergy B f = ∑ y ∈ B, f y * (2 * d * f y - ∑ a : Dir d, f (y + dirVec a)) := by
  rw [edgeEnergy, energy_eq B (siteNbhd B) f hf (subset_siteNbhd B)
    (fun z hz v hv => add_mem_siteNbhd hz hv)]
  have : ∀ y : Site d, ∑ v ∈ dirs d, f (y + v) = ∑ a : Dir d, f (y + dirVec a) :=
    fun y => sum_dirs (fun v => f (y + v))
  simp only [this]
  ring

theorem edgeEnergy_nonneg (B : Finset (Site d)) (f : Site d → ℝ) : 0 ≤ edgeEnergy B f := by
  rw [edgeEnergy, energy]
  have : 0 ≤ ∑ y ∈ siteNbhd B, ∑ v ∈ dirs d, (f y - f (y + v)) ^ 2 :=
    Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun v _ => sq_nonneg _
  linarith

/-- **The energy of the unit voltage is `1 / Reff`.** -/
theorem edgeEnergy_voltage (hd : 1 ≤ d) {A : Finset (Site d)} {x : Site d} (hx : x ∉ A) :
    edgeEnergy (insert x A) (voltage A x) = 1 / Reff A x := by
  obtain ⟨hv1, hv0, hvh⟩ := isUnitVoltage_voltage hd hx
  rw [edgeEnergy_eq (insert x A) hv0, Finset.sum_insert hx]
  have hA : ∑ y ∈ A, voltage A x y * (2 * d * voltage A x y
      - ∑ a : Dir d, voltage A x (y + dirVec a)) = 0 :=
    Finset.sum_eq_zero fun y hy => by rw [hvh y hy, sub_self, mul_zero]
  rw [hA, add_zero, hv1, one_mul, ← currentOut_voltage hd hx, currentOut, Finset.sum_sub_distrib,
    Finset.sum_const, card_dir, nsmul_eq_mul, hv1]
  push_cast
  ring

/-- **The Dirichlet principle.** Every voltage that is `1` at `x` and `0` off `A⁺` has energy at
least `1 / Reff(x ↔ (A⁺)^c)`. -/
theorem one_div_reff_le_edgeEnergy (hd : 1 ≤ d) {A : Finset (Site d)} {x : Site d} (hx : x ∉ A)
    {f : Site d → ℝ} (hf1 : f x = 1) (hf0 : ∀ z, z ∉ insert x A → f z = 0) :
    1 / Reff A x ≤ edgeEnergy (insert x A) f := by
  obtain ⟨hv1, hv0, hvh⟩ := isUnitVoltage_voltage hd hx
  have hEv := edgeEnergy_voltage hd hx
  set v := voltage A x with hvdef
  set w : Site d → ℝ := fun z => f z - v z with hwdef
  have hw0 : ∀ z, z ∉ insert x A → w z = 0 := by
    intro z hz
    simp only [hwdef]
    rw [hf0 z hz, hv0 z hz, sub_self]
  have hwx : w x = 0 := by
    simp only [hwdef]
    rw [hf1, hv1, sub_self]
  have hfy : ∀ z, f z = v z + w z := fun z => by
    simp only [hwdef]
    ring
  have hpt : ∀ y, f y * (2 * d * f y - ∑ a : Dir d, f (y + dirVec a))
      = v y * (2 * d * v y - ∑ a : Dir d, v (y + dirVec a))
        + w y * (2 * d * w y - ∑ a : Dir d, w (y + dirVec a))
        + 2 * (w y * (2 * d * v y)) - w y * ∑ a : Dir d, v (y + dirVec a)
        - v y * ∑ a : Dir d, w (y + dirVec a) := by
    intro y
    have hs : ∑ a : Dir d, f (y + dirVec a)
        = ∑ a : Dir d, v (y + dirVec a) + ∑ a : Dir d, w (y + dirVec a) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => hfy _
    rw [hs, hfy y]
    ring
  have hexp : edgeEnergy (insert x A) f
      = edgeEnergy (insert x A) v + edgeEnergy (insert x A) w
        + 2 * ∑ y ∈ insert x A, w y * (2 * d * v y)
        - ∑ y ∈ insert x A, w y * ∑ a : Dir d, v (y + dirVec a)
        - ∑ y ∈ insert x A, v y * ∑ a : Dir d, w (y + dirVec a) := by
    rw [edgeEnergy_eq (insert x A) hf0, edgeEnergy_eq (insert x A) hv0,
      edgeEnergy_eq (insert x A) hw0, Finset.sum_congr rfl (fun y _ => hpt y), Finset.mul_sum]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hcross : ∑ y ∈ insert x A, w y * (2 * d * v y)
      - ∑ y ∈ insert x A, w y * ∑ a : Dir d, v (y + dirVec a) = 0 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_insert hx, hwx, zero_mul, zero_mul, sub_zero,
      zero_add]
    exact Finset.sum_eq_zero fun y hy => by rw [hvh y hy, sub_self]
  have hsymm := sum_mul_sum_dir_symm (insert x A) hv0 hw0
  linarith [edgeEnergy_nonneg (insert x A) w]

/-! ### Lemma 2.2 with the electrical effective resistance -/

/-- **Lemma 2.2 (`lem:schur`), with the effective resistance of the electrical network.** For
`d ≥ 1`, a finite `A ⊂ ℤ^d` and `x ∉ A`, the effective resistance `R` between `x` and the
grounded complement of `A⁺ = A ∪ {x}` in `ℤ^d` with unit conductances satisfies
`R = -Δ_{A⁺}^{-1}(x,x) ≥ 1/(2d)` and `u_{A⁺}(x) = R h_A(x)`; moreover
`T(A⁺) - T(A) = h_A(x) u_{A⁺}(x)`, `h_A(x)^2 ≤ 2d (T(A⁺) - T(A))` and
`u_{A⁺}(x)^2 = R (T(A⁺) - T(A))`. By the Dirichlet principle `1 / R` is the least energy of a
voltage equal to `1` at `x` and to `0` off `A⁺`, attained by the unit voltage. -/
theorem one_point_insertion_electrical (hd : 1 ≤ d) (A : Finset (Site d)) (x : Site d)
    (hx : x ∉ A) :
    effResistance A x = -((dirichletLaplacian (insert x A))⁻¹
        ⟨x, Finset.mem_insert_self x A⟩ ⟨x, Finset.mem_insert_self x A⟩) ∧
      1 / (2 * (d : ℝ)) ≤ effResistance A x ∧
      u (insert x A) x = effResistance A x * LatticeProb.h A x ∧
      T (insert x A) - T A = LatticeProb.h A x * u (insert x A) x ∧
      LatticeProb.h A x ^ 2 ≤ 2 * (d : ℝ) * (T (insert x A) - T A) ∧
      u (insert x A) x ^ 2 = effResistance A x * (T (insert x A) - T A) ∧
      (∀ f : Site d → ℝ, f x = 1 → (∀ z, z ∉ insert x A → f z = 0) →
        1 / effResistance A x ≤ edgeEnergy (insert x A) f) ∧
      edgeEnergy (insert x A) (voltage A x) = 1 / effResistance A x := by
  rw [effResistance_eq_Reff hd hx]
  obtain ⟨hu, hT, hR, hh, hu2⟩ := ORRW.Frozen.one_point_insertion hd A x hx
  exact ⟨rfl, hR, hu, hT, hh, hu2, fun f hf1 hf0 => one_div_reff_le_edgeEnergy hd hx hf1 hf0,
    edgeEnergy_voltage hd hx⟩

end ORRW.Electrical
