/-
Supporting lemmas for the one-point insertion lemma of Bou-Rabee--Peres,
Section 2, `orrw.tex` (label `lem:schur`).

Nothing here is frozen.  The route is the one recorded in
The route taken here is to work with the defining equations
of `u` rather than with a Schur complement, which Mathlib does not have.

* `dirichletLaplacian_mulVec_apply` rewrites `Δ_A v` at a point as the lattice
  Laplacian of the zero-extension of `v`.

* `maximum_principle` is the `Δ_A v ≥ 0 ⟹ v ≤ 0` form of the comparison
  argument already used for `dirichletLaplacian_isUnit`.

* `harmonic_sum` is the heart: a function vanishing off `A ∪ {p}` and harmonic
  on `A` satisfies `∑_{y ∈ A} f y = f(p)(h_A(p) - 1)`.  The proof solves the
  Dirichlet problem for `f|_A`, whose right-hand side is `-f(p)` times the
  indicator of the neighbours of `p`, and then uses the symmetry of `Δ_A⁻¹` to
  turn the resulting sum into `∑_{y ∼ p, y ∈ A} u_A(y) = h_A(p) - 1`.

  Both conjuncts of `lem:schur` are this one lemma applied to two functions:
  `u_{A⁺} - u_A` gives `eq:deltaT`, and the `x`-column of `Δ_{A⁺}⁻¹` gives
  `u_{A⁺}(x) = Reff·h_A(x)`.

* `1/(2d) ≤ Reff` comes from `(Δ_{A⁺} Δ_{A⁺}⁻¹)(x,x) = 1` together with
  `maximum_principle`, which makes the Green's function nonpositive in the sign
  convention of `dirichletLaplacian`.
-/
import Mathlib
import ORRW.Basic
import ORRW.Lattice

open Finset
open scoped Matrix

namespace ORRW.Support

variable {d : ℕ}

/-- Entrywise form of the action of `Δ_A` on a vector: the lattice Laplacian of
the zero-extension. -/
lemma dirichletLaplacian_mulVec_apply (A : Finset (Site d)) (v : A → ℝ) (y : A) :
    (dirichletLaplacian A *ᵥ v) y
      = (∑ a : Dir d, extendZero A v ((y : Site d) + dirVec a)) - 2 * d * v y := by
  have hgoff : ∀ z, z ∉ A → extendZero A v z = 0 :=
    fun z hz => extendZero_of_notMem A v hz
  have hsplit : (dirichletLaplacian A *ᵥ v) y
      = (∑ z : A, (if Adj (y : Site d) (z : Site d) then v z else 0))
        - ∑ z : A, (if y = z then (2 * d : ℝ) * v z else 0) := by
    rw [Matrix.mulVec, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [dirichletLaplacian, sub_mul, ite_mul, one_mul, zero_mul]
  have h2 : (∑ z : A, (if y = z then (2 * d : ℝ) * v z else 0)) = 2 * d * v y := by
    rw [Finset.sum_ite_eq Finset.univ y (fun z => (2 * d : ℝ) * v z)]
    simp
  have hlhs : (∑ z : A, (if Adj (y : Site d) (z : Site d) then v z else 0))
      = ∑ a : Dir d, extendZero A v ((y : Site d) + dirVec a) := by
    rw [← sum_adj_eq_sum_dir A (extendZero A v) hgoff, Finset.sum_filter,
      ← Finset.sum_coe_sort A
        (fun z => if Adj (y : Site d) z then extendZero A v z else 0)]
    exact Finset.sum_congr rfl fun z _ => by rw [extendZero_coe]
  rw [hsplit, h2, hlhs]

/-- Maximum principle: a subsolution of the Dirichlet problem is nonpositive.
The comparison function is the one used in `dirichletLaplacian_isUnit`. -/
lemma maximum_principle (hd : 0 < d) (A : Finset (Site d)) (v : A → ℝ)
    (hv : ∀ y : A, 0 ≤ (dirichletLaplacian A *ᵥ v) y) : ∀ y : A, v y ≤ 0 := by
  intro x₁
  by_contra hpos
  push_neg at hpos
  obtain ⟨j₀⟩ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨B, hB⟩ : ∃ B : Finset (Site d),
      B = A ∪ A.biUnion (fun y => univ.image (fun a : Dir d => y + dirVec a)) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 1 + ∑ z ∈ B, ((z j₀ : ℤ) : ℝ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Site d → ℝ, ∀ y, w y = K - ((y j₀ : ℤ) : ℝ) ^ 2 :=
    ⟨_, fun _ => rfl⟩
  have hwpos : ∀ y ∈ B, 0 < w y := by
    intro y hy
    have h1 : ((y j₀ : ℤ) : ℝ) ^ 2 ≤ ∑ z ∈ B, ((z j₀ : ℤ) : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun z : Site d => ((z j₀ : ℤ) : ℝ) ^ 2)
        (fun z _ => sq_nonneg _) hy
    rw [hw, hK]
    linarith
  have hAB : ∀ y ∈ A, y ∈ B := by
    intro y hy
    rw [hB]
    exact Finset.mem_union_left _ hy
  have hnbrB : ∀ y ∈ A, ∀ a : Dir d, y + dirVec a ∈ B := by
    intro y hy a
    rw [hB]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2
      ⟨y, hy, Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩)
  have hlap : ∀ x : Site d, ∑ a : Dir d, w (x + dirVec a) = 2 * d * w x - 2 := by
    intro x
    simp only [hw]
    rw [Finset.sum_sub_distrib, Finset.sum_const, sum_sq_shift x j₀]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hgoff : ∀ y, y ∉ A → extendZero A v y = 0 :=
    fun y hy => extendZero_of_notMem A v hy
  have heq : ∀ x : A, 2 * d * v x
      ≤ ∑ a : Dir d, extendZero A v ((x : Site d) + dirVec a) := by
    intro x
    have h := hv x
    rw [dirichletLaplacian_mulVec_apply A v x] at h
    linarith
  have hAne : Nonempty A := ⟨x₁⟩
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max (fun x : A => v x / w (x : Site d))
  have hwx₁ : 0 < w (x₁ : Site d) := hwpos _ (hAB _ x₁.2)
  have hwx₀ : 0 < w (x₀ : Site d) := hwpos _ (hAB _ x₀.2)
  have htpos : 0 < v x₀ / w (x₀ : Site d) :=
    lt_of_lt_of_le (div_pos hpos hwx₁) (hx₀ x₁)
  have hgle : ∀ y ∈ B, extendZero A v y ≤ (v x₀ / w (x₀ : Site d)) * w y := by
    intro y hyB
    by_cases hy : y ∈ A
    · have hmax := hx₀ ⟨y, hy⟩
      have hwy : 0 < w y := hwpos y hyB
      rw [div_le_iff₀ hwy] at hmax
      have hc : extendZero A v y = v ⟨y, hy⟩ := extendZero_coe A v ⟨y, hy⟩
      rw [hc]
      exact hmax
    · rw [hgoff y hy]
      exact le_of_lt (mul_pos htpos (hwpos y hyB))
  have hstep : ∑ a : Dir d, extendZero A v ((x₀ : Site d) + dirVec a)
      ≤ ∑ a : Dir d, (v x₀ / w (x₀ : Site d)) * w ((x₀ : Site d) + dirVec a) :=
    Finset.sum_le_sum fun a _ => hgle _ (hnbrB _ x₀.2 a)
  rw [← Finset.mul_sum, hlap] at hstep
  have hcancel : v x₀ / w (x₀ : Site d) * w (x₀ : Site d) = v x₀ :=
    div_mul_cancel₀ _ (ne_of_gt hwx₀)
  nlinarith [heq x₀, hstep, htpos, hcancel]

/-! ## Symmetry -/

/-- The Dirichlet Laplacian on a finite set of sites is symmetric, the fact underlying the use of Δ_A⁻¹ to convert the harmonic sum into a potential sum. -/
lemma dirichletLaplacian_transpose (A : Finset (Site d)) :
    (dirichletLaplacian A)ᵀ = dirichletLaplacian A := by
  funext y z
  simp only [Matrix.transpose_apply, dirichletLaplacian]
  congr 1
  · exact if_congr (adj_comm _ _) rfl rfl
  · exact if_congr eq_comm rfl rfl

/-- Symmetry of the inverse Dirichlet Laplacian, the fact underpinning the harmonic-sum argument that converts the solved Dirichlet problem into the identity h_A(p) − 1. -/
lemma dirichletLaplacian_inv_symm (A : Finset (Site d)) (y z : A) :
    (dirichletLaplacian A)⁻¹ y z = (dirichletLaplacian A)⁻¹ z y := by
  have h : ((dirichletLaplacian A)⁻¹)ᵀ = (dirichletLaplacian A)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, dirichletLaplacian_transpose]
  exact congrFun (congrFun h.symm y) z

/-! ## The defining equation of `u` -/

/-- Extends a charge on the finite site set by zero to the whole lattice so that the lattice Laplacian and the Dirichlet Laplacian agree at points of the set. -/
lemma extendZero_u (A : Finset (Site d)) :
    extendZero A (fun z : A => u A (z : Site d)) = u A := by
  funext z
  by_cases hz : z ∈ A
  · rw [show z = ((⟨z, hz⟩ : A) : Site d) from rfl, extendZero_coe]
  · rw [extendZero_of_notMem A _ hz, u, extendZero_of_notMem A _ hz]

/-- Relates the Dirichlet Laplacian on a finite site set to the lattice Laplacian of the zero-extension, providing the rewriting step used to transfer the defining equations of the potential into the one-point insertion argument. -/
lemma u_mulVec (hd : 0 < d) (A : Finset (Site d)) :
    dirichletLaplacian A *ᵥ (fun z : A => u A (z : Site d)) = fun _ => (-1 : ℝ) := by
  have hres : (fun z : A => u A (z : Site d))
      = (-(dirichletLaplacian A)⁻¹) *ᵥ (fun _ => (1:ℝ)) := by
    funext z
    exact extendZero_coe A _ z
  rw [hres, Matrix.mulVec_mulVec, Matrix.mul_neg,
    Matrix.mul_nonsing_inv _ (dirichletLaplacian_isUnit hd A)]
  rw [Matrix.neg_mulVec, Matrix.one_mulVec]
  rfl

/-- The Dirichlet Green function on the finite site set A is harmonic away from its pole, i.e. its lattice Laplacian vanishes at every interior point of A. -/
lemma u_lap (hd : 0 < d) (A : Finset (Site d)) (y : Site d) (hy : y ∈ A) :
    (∑ a : Dir d, u A (y + dirVec a)) = 2 * d * u A y - 1 := by
  have h := dirichletLaplacian_mulVec_apply A (fun z : A => u A (z : Site d)) ⟨y, hy⟩
  rw [u_mulVec hd A] at h
  simp only [extendZero_u] at h
  linarith [h]

/-! ## The key summation lemma -/

/-- If `f` vanishes off `A ∪ {p}` and is discrete-harmonic at every point of
`A`, then `∑_{y ∈ A} f y = f(p) (h_A(p) - 1)`.  This is the step of `lem:schur`
that turns the symmetry of `-Δ_A⁻¹` into `h_A`. -/
lemma harmonic_sum (hd : 0 < d) (A : Finset (Site d)) (p : Site d) (hp : p ∉ A)
    (f : Site d → ℝ) (hoff : ∀ z, z ∉ insert p A → f z = 0)
    (hharm : ∀ y ∈ A, (∑ a : Dir d, f (y + dirVec a)) = 2 * d * f y) :
    ∑ y ∈ A, f y = f p * (ORRW.h A p - 1) := by
  classical
  have hLu : IsUnit (dirichletLaplacian A).det := dirichletLaplacian_isUnit hd A
  set φ : A → ℝ := fun y => f (y : Site d) with hφ
  set χ : A → ℝ := fun y => if Adj (y : Site d) p then 1 else 0 with hχ
  have hchi : ∀ y : Site d, (∑ a : Dir d, (if (y + dirVec a) = p then f p else 0))
      = if Adj y p then f p else 0 := by
    intro y
    have hg : ∀ z, z ∉ ({p} : Finset (Site d)) → (if z = p then f p else 0) = 0 := by
      intro z hz
      simp only [Finset.mem_singleton] at hz
      rw [if_neg hz]
    rw [← sum_adj_eq_sum_dir ({p} : Finset (Site d)) (fun z => if z = p then f p else 0) hg y,
      Finset.filter_singleton]
    by_cases hap : Adj y p
    · rw [if_pos hap, if_pos hap]
      simp
    · rw [if_neg hap, if_neg hap]
      simp
  have hext : ∀ z : Site d, extendZero A φ z = f z - (if z = p then f p else 0) := by
    intro z
    by_cases hz : z ∈ A
    · have hzp : z ≠ p := fun hzp => hp (hzp ▸ hz)
      rw [show z = ((⟨z, hz⟩ : A) : Site d) from rfl, extendZero_coe, if_neg hzp]
      simp [hφ]
    · rw [extendZero_of_notMem A φ hz]
      by_cases hzp : z = p
      · rw [if_pos hzp, hzp]
        ring
      · rw [if_neg hzp, hoff z (by simp [Finset.mem_insert, hzp, hz]), sub_zero]
  have hmv : dirichletLaplacian A *ᵥ φ = (-(f p)) • χ := by
    funext y
    rw [dirichletLaplacian_mulVec_apply A φ y]
    have h1 : ∑ a : Dir d, extendZero A φ ((y : Site d) + dirVec a)
        = (∑ a : Dir d, f ((y : Site d) + dirVec a))
          - (if Adj (y : Site d) p then f p else 0) := by
      rw [← hchi ((y : Site d)), ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => hext _
    rw [h1, hharm (y : Site d) y.2]
    show _ = (-(f p)) * (if Adj (y : Site d) p then (1:ℝ) else 0)
    have hy : φ y = f (y : Site d) := rfl
    rw [hy]
    by_cases hap : Adj (y : Site d) p <;> simp [hap]
  have hphi : φ = (-(f p)) • ((dirichletLaplacian A)⁻¹ *ᵥ χ) := by
    have hh := congrArg (fun v => (dirichletLaplacian A)⁻¹ *ᵥ v) hmv
    simp only [Matrix.mulVec_mulVec] at hh
    rw [Matrix.nonsing_inv_mul _ hLu, Matrix.one_mulVec] at hh
    rw [hh, Matrix.mulVec_smul]
  have hrow : ∀ z : A, (∑ y : A, (dirichletLaplacian A)⁻¹ y z) = -(u A (z : Site d)) := by
    intro z
    have hs : (∑ y : A, (dirichletLaplacian A)⁻¹ y z)
        = ∑ y : A, (dirichletLaplacian A)⁻¹ z y :=
      Finset.sum_congr rfl fun y _ => dirichletLaplacian_inv_symm A y z
    have hu : u A (z : Site d) = ((-(dirichletLaplacian A)⁻¹) *ᵥ (fun _ => (1:ℝ))) z :=
      extendZero_coe A _ z
    rw [hs, hu]
    simp [Matrix.mulVec, dotProduct]
  have hsum : ∑ y : A, ((dirichletLaplacian A)⁻¹ *ᵥ χ) y = -(ORRW.h A p - 1) := by
    have hstep : ∀ y : A, ((dirichletLaplacian A)⁻¹ *ᵥ χ) y
        = ∑ z : A, (dirichletLaplacian A)⁻¹ y z * χ z := fun _ => rfl
    rw [Finset.sum_congr rfl (fun y _ => hstep y), Finset.sum_comm]
    have h2 : ∀ z : A, (∑ y : A, (dirichletLaplacian A)⁻¹ y z * χ z)
        = (-(u A (z : Site d))) * χ z := by
      intro z
      rw [← Finset.sum_mul, hrow z]
    rw [Finset.sum_congr rfl (fun z _ => h2 z)]
    have hconv : (∑ z : A, (-(u A (z : Site d))) * χ z)
        = ∑ z ∈ A, (-(u A z)) * (if Adj z p then (1:ℝ) else 0) :=
      Finset.sum_coe_sort A (fun z => (-(u A z)) * (if Adj z p then (1:ℝ) else 0))
    rw [hconv]
    unfold ORRW.h
    rw [Finset.sum_filter]
    rw [show -((1 + ∑ a ∈ A, if Adj a p then u A a else 0) - 1)
        = -(∑ a ∈ A, if Adj a p then u A a else 0) by ring, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : Adj z p <;> simp [hz]
  have hfin : ∑ y ∈ A, f y = ∑ y : A, φ y := (Finset.sum_coe_sort A f).symm
  rw [hfin, hphi]
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hsum]
  ring

/-- The mean exit time is nonnegative.  `Δ_A u_A = -1 ≤ 0`, so `-u_A` is a
subsolution and `maximum_principle` applies. -/
lemma u_nonneg (hd : 0 < d) (A : Finset (Site d)) (y : Site d) : 0 ≤ u A y := by
  by_cases hy : y ∈ A
  · have hsub : ∀ w : A, 0 ≤ (dirichletLaplacian A *ᵥ (fun z : A => -(u A (z : Site d)))) w := by
      intro w
      have hneg : (fun z : A => -(u A (z : Site d))) = -(fun z : A => u A (z : Site d)) := rfl
      rw [hneg, Matrix.mulVec_neg, u_mulVec hd A]
      norm_num
    have hle := maximum_principle hd A (fun z : A => -(u A (z : Site d))) hsub ⟨y, hy⟩
    simpa using hle
  · have hz : u A y = 0 := extendZero_of_notMem A _ hy
    rw [hz]

/-- The hitting potential of a site is at least one, the lower bound on the walk's expected visits that feeds the resistance estimate. -/
lemma one_le_h (hd : 0 < d) (A : Finset (Site d)) (x : Site d) : 1 ≤ ORRW.h A x := by
  have : 0 ≤ ∑ y ∈ A with Adj y x, u A y :=
    Finset.sum_nonneg fun y _ => u_nonneg hd A y
  unfold ORRW.h
  linarith

/-! ## The Green's function of `insert x A` at `x` -/

/-- The `ξ`-column of `Δ_B⁻¹`, extended by zero. -/
noncomputable def green (B : Finset (Site d)) (ξ : B) : Site d → ℝ :=
  extendZero B (fun z : B => (dirichletLaplacian B)⁻¹ z ξ)

/-- The Dirichlet Laplacian on a finite site set composed with its inverse recovers the Green function, i.e. the potential of a unit charge at ξ evaluated at w equals the inverse matrix entry. -/
lemma green_mulVec (hd : 0 < d) (B : Finset (Site d)) (ξ w : B) :
    (dirichletLaplacian B *ᵥ (fun z : B => (dirichletLaplacian B)⁻¹ z ξ)) w
      = if w = ξ then 1 else 0 := by
  have hmul : (dirichletLaplacian B *ᵥ (fun z : B => (dirichletLaplacian B)⁻¹ z ξ)) w
      = ((dirichletLaplacian B) * (dirichletLaplacian B)⁻¹) w ξ := by
    rw [Matrix.mul_apply]
    rfl
  rw [hmul, Matrix.mul_nonsing_inv _ (dirichletLaplacian_isUnit hd B), Matrix.one_apply]

/-- Expresses the harmonic identity that summing the Green function over the neighbours of a site in the range recovers the potential at that site, the key step behind the one-point insertion lemma. -/
lemma green_lap (hd : 0 < d) (B : Finset (Site d)) (ξ : B) (y : Site d) (hy : y ∈ B) :
    (∑ a : Dir d, green B ξ (y + dirVec a))
      = 2 * d * green B ξ y + (if (⟨y, hy⟩ : B) = ξ then 1 else 0) := by
  have hmv := dirichletLaplacian_mulVec_apply B
    (fun z : B => (dirichletLaplacian B)⁻¹ z ξ) ⟨y, hy⟩
  rw [green_mulVec hd B ξ ⟨y, hy⟩] at hmv
  have hcoe : ((⟨y, hy⟩ : B) : Site d) = y := rfl
  rw [hcoe] at hmv
  have hg2 : extendZero B (fun z : B => (dirichletLaplacian B)⁻¹ z ξ) y
      = (dirichletLaplacian B)⁻¹ ⟨y, hy⟩ ξ := extendZero_coe B _ ⟨y, hy⟩
  simp only [green]
  rw [hg2]
  linarith [hmv]

/-- Identifies the Green operator on the finite site set as the inverse of the Dirichlet Laplacian, giving the kernel values used to express potentials and the effective resistance of the walk. -/
lemma green_apply_coe (B : Finset (Site d)) (ξ : B) (y : B) :
    green B ξ (y : Site d) = (dirichletLaplacian B)⁻¹ y ξ := extendZero_coe B _ y

/-- Identifies the entry of the inverse Dirichlet matrix on the extended site set with minus the Green function, supplying the symmetry identity that drives the harmonic-sum computation. -/
lemma Reff_eq_neg_green (A : Finset (Site d)) (x : Site d) :
    Reff A x = -green (insert x A) ⟨x, Finset.mem_insert_self x A⟩ x := by
  have hg : green (insert x A) ⟨x, Finset.mem_insert_self x A⟩ x
      = (dirichletLaplacian (insert x A))⁻¹ ⟨x, Finset.mem_insert_self x A⟩
          ⟨x, Finset.mem_insert_self x A⟩ :=
    green_apply_coe (insert x A) ⟨x, Finset.mem_insert_self x A⟩
      ⟨x, Finset.mem_insert_self x A⟩
  rw [hg, Reff]

/-- Averaging the Green kernel over the neighbours of a site in the box expresses the harmonic extension that feeds the one-point insertion computation. -/
lemma green_lap' (hd : 0 < d) (B : Finset (Site d)) (ξ : B) (y : Site d) (hy : y ∈ B) :
    (∑ a : Dir d, green B ξ (y + dirVec a))
      = 2 * d * green B ξ y + (if y = (ξ : Site d) then 1 else 0) := by
  rw [green_lap hd B ξ y hy]
  congr 1
  by_cases hc : y = (ξ : Site d)
  · rw [if_pos hc, if_pos (Subtype.ext hc)]
  · rw [if_neg hc, if_neg (fun hcon => hc (congrArg Subtype.val hcon))]

/-- The Green function on the finite box is nonpositive, providing the sign control needed for the comparison argument in the one-point insertion lemma. -/
lemma green_nonpos (hd : 0 < d) (B : Finset (Site d)) (ξ : B) (z : Site d) :
    green B ξ z ≤ 0 := by
  by_cases hz : z ∈ B
  · have hmp := maximum_principle hd B (fun z : B => (dirichletLaplacian B)⁻¹ z ξ)
      (by
        intro w
        rw [green_mulVec hd B ξ w]
        by_cases hw : w = ξ <;> simp [hw])
    have : green B ξ z = (dirichletLaplacian B)⁻¹ ⟨z, hz⟩ ξ := extendZero_coe B _ ⟨z, hz⟩
    rw [this]
    exact hmp ⟨z, hz⟩
  · rw [green, extendZero_of_notMem B _ hz]

/-! ## The one-point insertion lemma -/

/-- Delivers the one-point insertion lemma by expressing both the exit potential and the charge increment at the newly added site in terms of the harmonic measure and effective resistance of the original range. -/
theorem one_point_insertion (hd : 1 ≤ d)
    (A : Finset (Site d)) (x : Site d) (hx : x ∉ A) :
    u (insert x A) x = Reff A x * ORRW.h A x ∧
      T (insert x A) - T A = ORRW.h A x * u (insert x A) x ∧
      1 / (2 * (d : ℝ)) ≤ Reff A x := by
  classical
  have hd0 : 0 < d := hd
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
  set B : Finset (Site d) := insert x A with hB
  have hxB : x ∈ B := Finset.mem_insert_self x A
  set ξ : B := ⟨x, hxB⟩ with hξ
  have hAB : ∀ y, y ∈ A → y ∈ B := fun y hy => Finset.mem_insert_of_mem hy
  have huAx : u A x = 0 := extendZero_of_notMem A _ hx
  -- the Green's function part
  have hgx : green B ξ x = (dirichletLaplacian B)⁻¹ ξ ξ := extendZero_coe B _ ξ
  have hReff : Reff A x = -green B ξ x := by rw [hgx, Reff]
  have hgharm : ∀ y ∈ A, (∑ a : Dir d, green B ξ (y + dirVec a)) = 2 * d * green B ξ y := by
    intro y hy
    rw [green_lap hd0 B ξ y (hAB y hy)]
    have hne : (⟨y, hAB y hy⟩ : B) ≠ ξ := by
      intro hcon
      have hyx : y = x := congrArg Subtype.val hcon
      exact hx (hyx ▸ hy)
    rw [if_neg hne, add_zero]
  have hgoff : ∀ z, z ∉ insert x A → green B ξ z = 0 := by
    intro z hz
    rw [green, extendZero_of_notMem B _ (by rwa [hB])]
  have hgsum := harmonic_sum hd0 A x hx (green B ξ) hgoff hgharm
  -- first conjunct
  have huBx : u (insert x A) x = -(∑ z ∈ B, green B ξ z) := by
    have h1 : u B x = ((-(dirichletLaplacian B)⁻¹) *ᵥ (fun _ => (1:ℝ))) ξ :=
      extendZero_coe B _ ξ
    have h2 : ((-(dirichletLaplacian B)⁻¹) *ᵥ (fun _ => (1:ℝ))) ξ
        = -∑ z : B, (dirichletLaplacian B)⁻¹ ξ z := by
      simp [Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]
    have h3 : (∑ z : B, (dirichletLaplacian B)⁻¹ ξ z)
        = ∑ z : B, (dirichletLaplacian B)⁻¹ z ξ :=
      Finset.sum_congr rfl fun z _ => dirichletLaplacian_inv_symm B ξ z
    have h4 : (∑ z : B, (dirichletLaplacian B)⁻¹ z ξ) = ∑ z ∈ B, green B ξ z := by
      rw [← Finset.sum_coe_sort B (green B ξ)]
      simp only [green]
      exact Finset.sum_congr rfl fun z _ =>
        (extendZero_coe B (fun w : B => (dirichletLaplacian B)⁻¹ w ξ) z).symm
    rw [← hB, h1, h2, h3, h4]
  have hsplitg : (∑ z ∈ B, green B ξ z) = green B ξ x + ∑ z ∈ A, green B ξ z :=
    Finset.sum_insert (f := green B ξ) hx
  have hfirst : u (insert x A) x = Reff A x * ORRW.h A x := by
    rw [huBx, hsplitg, hgsum, hReff]
    ring
  -- second conjunct
  have hvoff : ∀ z, z ∉ insert x A → u B z - u A z = 0 := by
    intro z hz
    have h1 : u B z = 0 := extendZero_of_notMem B _ (by rwa [hB])
    have h2 : u A z = 0 :=
      extendZero_of_notMem A _ (fun hcon => hz (Finset.mem_insert_of_mem hcon))
    rw [h1, h2]
    ring
  have hvharm : ∀ y ∈ A, (∑ a : Dir d, (u B (y + dirVec a) - u A (y + dirVec a)))
      = 2 * d * (u B y - u A y) := by
    intro y hy
    rw [Finset.sum_sub_distrib, u_lap hd0 B y (hAB y hy), u_lap hd0 A y hy]
    ring
  have hvsum := harmonic_sum hd0 A x hx (fun z => u B z - u A z) hvoff hvharm
  have hTsplit : T (insert x A) = u B x + ∑ y ∈ A, u B y :=
    Finset.sum_insert (f := u B) hx
  have hsecond : T (insert x A) - T A = ORRW.h A x * u (insert x A) x := by
    rw [hTsplit, T, ← hB]
    have hsub : (∑ y ∈ A, u B y) - ∑ y ∈ A, u A y = ∑ y ∈ A, (u B y - u A y) := by
      rw [Finset.sum_sub_distrib]
    have := hvsum
    simp only [huAx, sub_zero] at this
    rw [show u B x + (∑ y ∈ A, u B y) - ∑ y ∈ A, u A y
        = u B x + ((∑ y ∈ A, u B y) - ∑ y ∈ A, u A y) by ring, hsub, this]
    ring
  -- third conjunct
  have hthird : 1 / (2 * (d : ℝ)) ≤ Reff A x := by
    have hlap := green_lap hd0 B ξ x hxB
    rw [if_pos (by rw [hξ])] at hlap
    have hle : (∑ a : Dir d, green B ξ (x + dirVec a)) ≤ 0 :=
      Finset.sum_nonpos fun a _ => green_nonpos hd0 B ξ _
    rw [hReff]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hlap, hle]
  exact ⟨hfirst, hsecond, hthird⟩

end ORRW.Support
