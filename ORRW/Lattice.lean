/-
The deterministic lattice objects of Bou-Rabee--Peres, *Once-reinforced random
walk on `ℤ^d` has range exponent at least `d/(d+1)`*, Section 2, "The insertion
inequality" (`sec:insertion`), `orrw.tex`.

The section fixes continuous-time simple random walk on `ℤ^d` with rate `1`
along each edge and, for a finite `A ⊂ ℤ^d`, introduces the Dirichlet Laplacian
`Δ_A`, the mean exit time `u_A`, the quantity `h_A` of `eq:h-def`, the total
mass `T(A)` of `eq:torsion-def`, and the effective resistance appearing in
`eq:schur`.  This file encodes those objects; nothing probabilistic is used.

Modelling decisions.

* Ruling L-001 (`u` is linear algebra, not a probabilistic expectation).  The
  paper defines `u_A(x) := E_x τ_A` and then records `u_A = -Δ_A^{-1} 1`.  We
  take the linear-algebra formula as the definition, so that Section 2 is
  purely deterministic and no continuous-time process has to be built.

* Ruling L-002 (`Reff` is defined by the Schur identity).  The paper defines
  `Reff(x ↔ (A⁺)^c)` as an effective resistance and proves in `eq:schur` that
  it equals `-Δ_{A⁺}^{-1}(x,x)`.  We take that identity as the definition, and
  so `Reff A x` below is the resistance from `x` to the complement of
  `insert x A`.  The electrical-network content of `eq:schur` is therefore not
  formalized; the two remaining assertions of `lem:schur` are.

* Ruling L-003 (`extendZero`).  Functions on `A` are extended by zero to all of
  `ℤ^d`, as the paper does ("with `u_A = 0` off `A`"), through the auxiliary
  definition `extendZero`.

* Ruling L-004 (`Matrix.inv` junk value).  Mathlib's `Matrix.inv` is `0` on a
  singular matrix, so `u`, `T` and `Reff` would be identically zero if `Δ_A`
  were singular and every bound of this section would hold vacuously.
  `dirichletLaplacian_isUnit` below rules this out for `d ≥ 1`, by the
  maximum-principle form of the paper's negative-definiteness argument.
-/
import Mathlib
import ORRW.Basic

namespace ORRW

open Finset
open scoped Matrix

variable {d : ℕ}

/-! ## Adjacency -/

/-- Adjacency in `ℤ^d`: `x ~ y` when `y` is obtained from `x` by a unit step. -/
def Adj (x y : Site d) : Prop := ∃ a : Dir d, y = x + dirVec a

/-- Provides the decidability of the adjacency relation so that lattice sites and their edges can be used in computable constructions throughout the development. -/
instance decidableAdj : DecidableRel (Adj (d := d)) :=
  fun x y => inferInstanceAs (Decidable (∃ a : Dir d, y = x + dirVec a))

/-- States how a direction vector acts on a coordinate, giving the component needed to build the lattice edges and difference operators of the insertion inequality section. -/
lemma dirVec_apply (a : Dir d) (i : Fin d) :
    dirVec a i = if i = a.1 then (if a.2 then 1 else -1) else 0 := rfl

/-- Fixes the two possible unit directions of an edge in the lattice by giving the sign vector attached to each orientation flag. -/
lemma dirVec_self (j : Fin d) (s : Bool) :
    dirVec ((j, s) : Dir d) j = if s then 1 else -1 := by
  simp [dirVec_apply]

/-- Fixes the sign convention for the direction vector between two distinct coordinate sites, distinguishing the two orientations of an edge by the Boolean parameter. -/
lemma dirVec_of_ne {i j : Fin d} (s : Bool) (h : i ≠ j) :
    dirVec ((j, s) : Dir d) i = 0 := by
  simp [dirVec_apply, h]

/-- The `2d` unit steps are distinct. -/
lemma dirVec_injective : Function.Injective (dirVec (d := d)) := by
  rintro ⟨j, s⟩ ⟨k, t⟩ hjk
  have hj : j = k := by
    by_contra hne
    have h1 := congrFun hjk j
    rw [dirVec_self, dirVec_of_ne t hne] at h1
    cases s <;> norm_num at h1
  subst hj
  have h1 := congrFun hjk j
  rw [dirVec_self, dirVec_self] at h1
  cases s <;> cases t <;> simp_all

/-- Symmetry of the edge relation, so that neighbour sums and Dirichlet Laplacian computations may treat adjacency between sites as undirected. -/
lemma adj_comm (x y : Site d) : Adj x y ↔ Adj y x := by
  constructor <;> rintro ⟨a, rfl⟩ <;> refine ⟨(a.1, !a.2), ?_⟩ <;>
    · funext i
      simp only [dirVec_apply, Pi.add_apply]
      by_cases hi : i = a.1 <;> cases a.2 <;> simp [hi]

/-- Reindexing a neighbour sum by directions: if `g` vanishes off `A`, the sum
of `g` over the neighbours of `x` lying in `A` is the sum of `g` over the `2d`
unit steps from `x`. -/
lemma sum_adj_eq_sum_dir (A : Finset (Site d)) (g : Site d → ℝ)
    (hg : ∀ y, y ∉ A → g y = 0) (x : Site d) :
    ∑ y ∈ A with Adj x y, g y = ∑ a : Dir d, g (x + dirVec a) := by
  have hinj : Set.InjOn (fun a : Dir d => x + dirVec a)
      ((univ.filter fun a : Dir d => x + dirVec a ∈ A) : Finset (Dir d)) := by
    intro a _ b _ hab
    exact dirVec_injective (add_right_injective x hab)
  have himg : (univ.filter fun a : Dir d => x + dirVec a ∈ A).image
        (fun a : Dir d => x + dirVec a)
      = A.filter (fun y => Adj x y) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Adj]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨ha, a, rfl⟩
    · rintro ⟨hy, a, rfl⟩; exact ⟨a, hy, rfl⟩
  rw [← himg, Finset.sum_image hinj, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hA : x + dirVec a ∈ A
  · rw [if_pos hA]
  · rw [if_neg hA, hg _ hA]

/-- The sum of a fixed coordinate over the `2d` unit steps vanishes. -/
lemma sum_dirVec_coord (i : Fin d) : ∑ a : Dir d, ((dirVec a i : ℤ) : ℝ) = 0 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Fintype.sum_bool]
  by_cases hij : i = j
  · subst hij
    rw [dirVec_self, dirVec_self]
    norm_num
  · rw [dirVec_of_ne true hij, dirVec_of_ne false hij]
    norm_num

/-- The sum of the square of a fixed coordinate over the `2d` unit steps is `2`. -/
lemma sum_dirVec_sq (i : Fin d) : ∑ a : Dir d, ((dirVec a i : ℤ) : ℝ) ^ 2 = 2 := by
  rw [Fintype.sum_prod_type]
  have hj : ∀ j : Fin d, ∑ s : Bool, ((dirVec ((j, s) : Dir d) i : ℤ) : ℝ) ^ 2
      = if i = j then (2 : ℝ) else 0 := by
    intro j
    rw [Fintype.sum_bool]
    by_cases hij : i = j
    · subst hij
      rw [dirVec_self, dirVec_self, if_pos rfl]
      norm_num
    · rw [dirVec_of_ne true hij, dirVec_of_ne false hij, if_neg hij]
      norm_num
  simp_rw [hj]
  rw [Finset.sum_ite_eq Finset.univ i (fun _ => (2 : ℝ))]
  simp

/-- The lattice Laplacian of `y ↦ y_i^2` is the constant `2`. -/
lemma sum_sq_shift (x : Site d) (i : Fin d) :
    ∑ a : Dir d, (((x + dirVec a) i : ℤ) : ℝ) ^ 2
      = 2 * d * ((x i : ℤ) : ℝ) ^ 2 + 2 := by
  have hexp : ∀ a : Dir d, (((x + dirVec a) i : ℤ) : ℝ) ^ 2
      = ((x i : ℤ) : ℝ) ^ 2 + 2 * ((x i : ℤ) : ℝ) * ((dirVec a i : ℤ) : ℝ)
        + ((dirVec a i : ℤ) : ℝ) ^ 2 := by
    intro a
    simp only [Pi.add_apply]
    push_cast
    ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
    sum_dirVec_coord, sum_dirVec_sq]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, mul_zero]
  ring

/-! ## The Dirichlet Laplacian -/

/-- The Dirichlet Laplacian of a finite set, `orrw.tex`:

  "`(Δ_A f)(x) := ∑_{y ∈ A, y ∼ x} f(y) - 2d f(x)`  `(x ∈ A)`,

   so that `Δ_A` is the generator of the walk killed on leaving `A`."

As a matrix acting by `Δ_A *ᵥ f`, this is the entrywise formula below. -/
def dirichletLaplacian (A : Finset (Site d)) : Matrix A A ℝ :=
  fun x y => (if Adj (x : Site d) (y : Site d) then 1 else 0)
    - (if x = y then (2 * d : ℝ) else 0)

/-- Extension by zero of a function on `A` to all of `ℤ^d` (ruling L-003). -/
noncomputable def extendZero (A : Finset (Site d)) (v : A → ℝ) : Site d → ℝ :=
  fun y => if hy : y ∈ A then v ⟨y, hy⟩ else 0

@[simp] lemma extendZero_coe (A : Finset (Site d)) (v : A → ℝ) (y : A) :
    extendZero A v (y : Site d) = v y := by
  simp [extendZero]

/-- Provides the extension by zero of a function on a finite set of sites to a site outside it, used when comparing Dirichlet objects on a set with those on a larger one. -/
lemma extendZero_of_notMem (A : Finset (Site d)) (v : A → ℝ) {y : Site d} (hy : y ∉ A) :
    extendZero A v y = 0 := by
  simp [extendZero, hy]

/-- `Δ_A` is invertible for `d ≥ 1`, `orrw.tex`:

  "Extending a function `f` supported in `A` by zero and summing over the
   undirected edges of `ℤ^d`, `⟨f, Δ_A f⟩ = -∑_{{x,y}} (f(x) - f(y))^2`, and
   since a nonzero `f` supported in a finite set differs across some edge,
   `Δ_A` is symmetric and negative definite, hence invertible."

This is the guard against ruling L-004: without it `u`, `T` and `Reff` could all
be the junk value `0`.  The proof below replaces the energy identity by the
equivalent maximum principle against the comparison function
`w(y) = K - y_i^2`, whose lattice Laplacian is the constant `-2`. -/
theorem dirichletLaplacian_isUnit (hd : 0 < d) (A : Finset (Site d)) :
    IsUnit (dirichletLaplacian A).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v₀, hv₀, hv₀eq⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
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
  -- Every solution of the homogeneous equation is nonpositive.
  have key : ∀ v : A → ℝ, dirichletLaplacian A *ᵥ v = 0 → ∀ x : A, v x ≤ 0 := by
    intro v hv x₁
    by_contra hpos
    push_neg at hpos
    have hgoff : ∀ y, y ∉ A → extendZero A v y = 0 :=
      fun y hy => extendZero_of_notMem A v hy
    have heq : ∀ x : A, ∑ a : Dir d, extendZero A v ((x : Site d) + dirVec a)
        = 2 * d * v x := by
      intro x
      have hx : ∑ y : A, dirichletLaplacian A x y * v y = 0 := congrFun hv x
      have hsplit : ∑ y : A, dirichletLaplacian A x y * v y
          = (∑ y : A, (if Adj (x : Site d) (y : Site d) then v y else 0))
            - ∑ y : A, (if x = y then (2 * d : ℝ) * v y else 0) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        simp only [dirichletLaplacian, sub_mul, ite_mul, one_mul, zero_mul]
      have h2 : (∑ y : A, (if x = y then (2 * d : ℝ) * v y else 0)) = 2 * d * v x := by
        rw [Finset.sum_ite_eq Finset.univ x (fun y => (2 * d : ℝ) * v y)]
        simp
      have hlhs : (∑ y : A, (if Adj (x : Site d) (y : Site d) then v y else 0))
          = ∑ a : Dir d, extendZero A v ((x : Site d) + dirVec a) := by
        rw [← sum_adj_eq_sum_dir A (extendZero A v) hgoff, Finset.sum_filter,
          ← Finset.sum_coe_sort A
            (fun y => if Adj (x : Site d) y then extendZero A v y else 0)]
        exact Finset.sum_congr rfl fun y _ => by rw [extendZero_coe]
      rw [hsplit, h2, hlhs] at hx
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
    rw [heq x₀, ← Finset.mul_sum, hlap] at hstep
    have hcancel : v x₀ / w (x₀ : Site d) * w (x₀ : Site d) = v x₀ :=
      div_mul_cancel₀ _ (ne_of_gt hwx₀)
    nlinarith [hstep, htpos, hcancel]
  have h1 := key v₀ hv₀eq
  have h2 := key (-v₀) (by rw [Matrix.mulVec_neg, hv₀eq, neg_zero])
  refine hv₀ (funext fun x => le_antisymm (h1 x) ?_)
  have := h2 x
  simp only [Pi.neg_apply, neg_nonpos] at this
  simpa using this

/-! ## Mean exit time, `h`, total mass, effective resistance -/

/-- The mean exit time `u_A`, `orrw.tex`:

  "`u_A(x) := E_x τ_A`  `(x ∈ A)` ... By the first-step analysis, `u_A` solves
   the Dirichlet problem `Δ_A u_A = -1_A` on `A`, with `u_A = 0` off `A`, so
   `u_A = -Δ_A^{-1} 1_A`."

Defined by the linear-algebra formula (ruling L-001), extended by zero. -/
noncomputable def u (A : Finset (Site d)) : Site d → ℝ :=
  extendZero A ((-(dirichletLaplacian A)⁻¹) *ᵥ (fun _ => 1))

/-- `h_A`, `orrw.tex` (`eq:h-def`):

  "For `x ∉ A` define `h_A(x) := 1 + ∑_{y ∈ A, y ∼ x} u_A(y)`." -/
noncomputable def h (A : Finset (Site d)) (x : Site d) : ℝ :=
  1 + ∑ y ∈ A with Adj y x, u A y

/-- The total mass `T(A)`, `orrw.tex` (`eq:torsion-def`):

  "`T(A) := ∑_{x ∈ A} u_A(x)`", with `T(∅) := 0`. -/
noncomputable def T (A : Finset (Site d)) : ℝ := ∑ x ∈ A, u A x

/-- The effective resistance from `x` to the grounded complement of
`A⁺ = A ∪ {x}`, `orrw.tex` (`eq:schur`):

  "`Reff(x ↔ (A⁺)^c) = -Δ_{A⁺}^{-1}(x,x) ≥ 1/(2d)`".

Taken as the definition (ruling L-002). -/
noncomputable def Reff (A : Finset (Site d)) (x : Site d) : ℝ :=
  -((dirichletLaplacian (insert x A))⁻¹
      ⟨x, Finset.mem_insert_self x A⟩ ⟨x, Finset.mem_insert_self x A⟩)

end ORRW
