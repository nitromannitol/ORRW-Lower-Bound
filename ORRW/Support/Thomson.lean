/-
Supporting lemmas for the resistance packing bound of Bou-Rabee--Peres,
Section 2, `orrw.tex` (label `lem:packing`).

Nothing here is frozen.  Under ruling L-002 `Reff A x` is the matrix entry
`-Δ_{A⁺}^{-1}(x,x)`, so the paper's appeal to Thomson's principle has to be
replaced by something provable from that definition.  Mathlib has no electrical
network theory, so the flow argument is carried out by hand, in the only case
the proof needs, namely a unit flow along a single path:

* `energy_eq` is the discrete Dirichlet identity: for `f` supported in `B`,
  the directed energy `∑_y ∑_v (f y - f (y+v))^2` equals
  `2 ∑_{y ∈ B} f y (2d f y - ∑_v f(y+v))`, i.e. twice `⟨f, -Δ_B f⟩`.  Applied
  to `f = -green`, whose Laplacian is a point mass at `x`, the energy is
  `2 Reff`.

* `gpath` is the coordinate-by-coordinate lattice geodesic from `x` to a point
  `p`, obtained by iterating a single "correct the first wrong coordinate"
  step.  Its vertices are distinct because their `ℓ¹` distance to `p`
  decreases by exactly one at each step.

* `value_sq_le` telescopes `f` along that geodesic and applies Cauchy--Schwarz,
  giving `(f x)^2 ≤ L · energy`.  With `energy = 2 f x` this is
  `Reff ≤ 2L` (`reff_le_nrm1`), the factor `2` coming from counting each edge
  in both directions rather than once.

* `packing_count` is the paper's disjointness argument, with `ℓ¹` balls
  replaced by the axis-aligned boxes `qbox`, which are easier to count and
  still fit inside `ℓ¹` balls.

* `resistance_packing_aux` sums the layers `#{i : r < ρ i} ≤ M (2d)^d /(r+1)^2`
  against the telescoping series `∑ 1/(r(r+1)) = 1`, which converges because
  `d ≥ 2`.
-/
import Mathlib
import ORRW.Basic
import ORRW.Lattice
import ORRW.Support.Insertion
import ORRW.Support.InsertionSum

open Finset

namespace ORRW.Support

variable {d : ℕ}

/-- The `ℓ¹` norm of a lattice point, as a natural number. -/
def nrm1 (z : Site d) : ℕ := ∑ i, (z i).natAbs

/-- The ℓ¹ norm on sites vanishes exactly at the origin, so the geodesic's strictly decreasing distance-to-`p` invariant is well defined. -/
lemma nrm1_eq_zero_iff {z : Site d} : nrm1 z = 0 ↔ z = 0 := by
  constructor
  · intro h
    funext i
    have := (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)
    simpa [Int.natAbs_eq_zero] using this
  · rintro rfl
    simp [nrm1]

/-- Triangle inequality for the ℓ¹ norm on sites, used to control distances along lattice geodesics. -/
lemma nrm1_add_le (z w : Site d) : nrm1 (z + w) ≤ nrm1 z + nrm1 w := by
  rw [nrm1, nrm1, nrm1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

/-- Negating a site does not change its ℓ¹ weight, a symmetry fact used when comparing a path with its reversed orientation. -/
lemma nrm1_neg (z : Site d) : nrm1 (-z) = nrm1 z := by
  simp [nrm1]

/-- Provides the symmetry of the ℓ¹ distance between sites, used to show the geodesic's vertices are distinct. -/
lemma nrm1_sub_comm (z w : Site d) : nrm1 (z - w) = nrm1 (w - z) := by
  rw [← nrm1_neg (z - w), neg_sub]

open Classical in
/-- One step from `y` toward `p`: the unit vector correcting the first
coordinate in which `y` and `p` differ, or `0` if there is none. -/
noncomputable def towardVec (p y : Site d) : Site d :=
  if h : ∃ j : Fin d, y j ≠ p j then
    dirVec ((h.choose, decide (y h.choose < p h.choose)) : Dir d)
  else 0

/-- The correction step toward the target point is a genuine edge direction, ensuring the geodesic construction moves along an actual lattice edge at each stage. -/
lemma towardVec_isDir {p y : Site d} (hne : y ≠ p) :
    ∃ a : Dir d, towardVec p y = dirVec a := by
  classical
  have h : ∃ j : Fin d, y j ≠ p j := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  exact ⟨(h.choose, decide (y h.choose < p h.choose)), by rw [towardVec, dif_pos h]⟩

/-- Provides the single correction step of the lattice geodesic: a neighbor of y strictly closer to p, used to build the path along which the flow argument runs. -/
lemma nrm1_toward {p y : Site d} (hne : y ≠ p) :
    nrm1 (p - (y + towardVec p y)) + 1 = nrm1 (p - y) := by
  classical
  have h : ∃ j : Fin d, y j ≠ p j := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  set j := h.choose with hj
  have hjne : y j ≠ p j := h.choose_spec
  have hstep : towardVec p y = dirVec ((j, decide (y j < p j)) : Dir d) := by
    rw [towardVec, dif_pos h]
  have hsplit : ∀ z : Site d, nrm1 z = (z j).natAbs + ∑ i ∈ Finset.univ.erase j, (z i).natAbs := by
    intro z
    rw [nrm1, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hoff : ∀ i ∈ Finset.univ.erase j,
      ((p - (y + towardVec p y)) i).natAbs = ((p - y) i).natAbs := by
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp only [Pi.sub_apply, Pi.add_apply, hstep, dirVec_of_ne _ hij, add_zero]
  rw [hsplit (p - (y + towardVec p y)), hsplit (p - y),
    Finset.sum_congr rfl hoff]
  have hjval : ((p - (y + towardVec p y)) j).natAbs + 1 = ((p - y) j).natAbs := by
    have hv : (towardVec p y) j = if y j < p j then (1:ℤ) else -1 := by
      rw [hstep, dirVec_self]
      by_cases hlt : y j < p j <;> simp [hlt]
    have hpa : (p - (y + towardVec p y)) j = p j - (y j + (towardVec p y) j) := rfl
    have hpb : (p - y) j = p j - y j := rfl
    rw [hpa, hpb, hv]
    by_cases hlt : y j < p j
    · rw [if_pos hlt]
      omega
    · rw [if_neg hlt]
      have : p j < y j := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hjne)
      omega
  omega

/-! ## The geodesic -/

/-- Provides the lattice path from `x` to `p` along which the flow argument routes the unit current, with strictly decreasing ℓ¹ distance to `p` guaranteeing distinct vertices. -/
noncomputable def toward (p y : Site d) : Site d := y + towardVec p y

/-- The coordinate-by-coordinate geodesic from `x` to `p`. -/
noncomputable def gpath (p x : Site d) (k : ℕ) : Site d := (toward p)^[k] x

@[simp] lemma gpath_zero (p x : Site d) : gpath p x 0 = x := rfl

/-- Each step of the canonical lattice geodesic from x toward p is obtained by correcting one coordinate of the previous vertex. -/
lemma gpath_succ (p x : Site d) (k : ℕ) : gpath p x (k+1) = toward p (gpath p x k) := by
  rw [gpath, gpath, Function.iterate_succ_apply']

/-- Provides the key inductive step showing the geodesic construction strictly decreases the ℓ¹ distance to the target at each correction step. -/
lemma gpath_nrm1 (p x : Site d) : ∀ k : ℕ, k ≤ nrm1 (p - x) →
    nrm1 (p - gpath p x k) = nrm1 (p - x) - k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hn' : n ≤ nrm1 (p - x) := Nat.le_of_succ_le hn
    have hprev := ih hn'
    have hpos : 0 < nrm1 (p - gpath p x n) := by omega
    have hne : gpath p x n ≠ p := by
      intro hcon
      rw [hcon, sub_self] at hpos
      rw [nrm1_eq_zero_iff.mpr rfl] at hpos
      exact absurd hpos (lt_irrefl 0)
    have hstep := nrm1_toward (p := p) (y := gpath p x n) hne
    rw [gpath_succ, toward]
    omega

/-- The coordinate-by-coordinate geodesic has not yet reached its endpoint before the ℓ¹ distance to it is exhausted, so its vertices are distinct along the walk. -/
lemma gpath_ne {p x : Site d} {k : ℕ} (hk : k < nrm1 (p - x)) : gpath p x k ≠ p := by
  intro hcon
  have h := gpath_nrm1 p x k (le_of_lt hk)
  rw [hcon] at h
  simp only [sub_self] at h
  have : nrm1 (0 : Site d) = 0 := nrm1_eq_zero_iff.mpr rfl
  omega

/-- The coordinate-by-coordinate lattice geode from x to p reaches p after exactly the ℓ¹ distance between them many steps. -/
lemma gpath_end (p x : Site d) : gpath p x (nrm1 (p - x)) = p := by
  have h := gpath_nrm1 p x (nrm1 (p - x)) le_rfl
  simp only [Nat.sub_self] at h
  have h2 : p - gpath p x (nrm1 (p - x)) = 0 := nrm1_eq_zero_iff.mp h
  exact (sub_eq_zero.mp h2).symm

/-- The coordinate-by-coordinate geodesic toward p visits distinct sites at all times up to its length, which is what lets the telescoping along the path be summed without repeated vertices. -/
lemma gpath_injOn (p x : Site d) {k l : ℕ} (hk : k ≤ nrm1 (p - x)) (hl : l ≤ nrm1 (p - x))
    (h : gpath p x k = gpath p x l) : k = l := by
  have h1 := gpath_nrm1 p x k hk
  have h2 := gpath_nrm1 p x l hl
  rw [h] at h1
  omega

/-! ## The Dirichlet energy -/

/-- The `2d` unit steps, as a finset of lattice points. -/
def dirs (d : ℕ) : Finset (Site d) := Finset.univ.image (dirVec : Dir d → Site d)

/-- Provides the decomposition of a lattice sum into contributions from the 2d coordinate directions, the bookkeeping step behind the directed energy identity. -/
lemma sum_dirs {M : Type*} [AddCommMonoid M] (g : Site d → M) :
    ∑ v ∈ dirs d, g v = ∑ a : Dir d, g (dirVec a) :=
  Finset.sum_image (fun _ _ _ _ hab => dirVec_injective hab)

/-- The vector attached to a direction is a member of the finite set of all direction vectors, so sums over directions can be rewritten as sums over those vectors. -/
lemma dirVec_mem_dirs (a : Dir d) : dirVec a ∈ dirs d :=
  Finset.mem_image_of_mem _ (Finset.mem_univ a)

/-- Flipping a direction's orientation negates its associated unit vector, the basic antisymmetry fact used when cancelling opposing edge contributions in the flow argument. -/
lemma dirVec_neg (a : Dir d) : dirVec ((a.1, !a.2) : Dir d) = -dirVec a := by
  funext i
  simp only [dirVec_apply, Pi.neg_apply]
  by_cases hi : i = a.1 <;> cases a.2 <;> simp [hi]

/-- The direction set is symmetric under negation, so every edge of a walk can be traversed in both orientations when summing directed energy. -/
lemma neg_mem_dirs {v : Site d} (hv : v ∈ dirs d) : -v ∈ dirs d := by
  rw [dirs, Finset.mem_image] at hv
  obtain ⟨a, _, rfl⟩ := hv
  rw [← dirVec_neg a]
  exact dirVec_mem_dirs _

/-- The directed Dirichlet energy of `f` over a finite index set of base
points. -/
def energy (V : Finset (Site d)) (f : Site d → ℝ) : ℝ :=
  ∑ y ∈ V, ∑ v ∈ dirs d, (f y - f (y + v))^2

/-- Provides the discrete Dirichlet identity that computes the directed energy of a function supported in B as twice its pairing with the boxed Laplacian, the key step for reading off the effective resistance from the Green function. -/
lemma energy_eq (B V : Finset (Site d)) (f : Site d → ℝ)
    (hf : ∀ z, z ∉ B → f z = 0) (hBV : B ⊆ V)
    (hnb : ∀ z ∈ B, ∀ v ∈ dirs d, z + v ∈ V) :
    energy V f
      = 2 * ∑ y ∈ B, f y * (2 * (d:ℝ) * f y - ∑ v ∈ dirs d, f (y + v)) := by
  classical
  have hcard : (dirs d).card = 2 * d := by
    rw [dirs, Finset.card_image_of_injective _ dirVec_injective, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    ring
  -- the three pieces
  have hVB : ∑ y ∈ V, (f y)^2 = ∑ y ∈ B, (f y)^2 := by
    refine (Finset.sum_subset hBV ?_).symm
    intro z _ hz
    rw [hf z hz]
    ring
  have hshift : ∀ v ∈ dirs d, ∑ y ∈ V, (f (y + v))^2 = ∑ y ∈ B, (f y)^2 := by
    intro v hv
    have hinj : ∀ a ∈ V, ∀ b ∈ V, a + v = b + v → a = b := by
      intro _ _ _ _ hab
      exact add_right_cancel hab
    have himg : ∑ z ∈ V.image (fun y => y + v), (f z)^2 = ∑ y ∈ V, (f (y + v))^2 :=
      Finset.sum_image hinj
    rw [← himg]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro z hz
      refine Finset.mem_image.mpr ⟨z + (-v), hnb z hz (-v) (neg_mem_dirs hv), by abel⟩
    · intro z _ hz
      rw [hf z hz]
      ring
  have hcross : ∑ y ∈ V, ∑ v ∈ dirs d, f y * f (y + v)
      = ∑ y ∈ B, ∑ v ∈ dirs d, f y * f (y + v) := by
    refine (Finset.sum_subset hBV ?_).symm
    intro z _ hz
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [hf z hz]
    ring
  -- expand
  have hexp : energy V f
      = (∑ y ∈ V, ∑ v ∈ dirs d, (f y)^2)
        - 2 * (∑ y ∈ V, ∑ v ∈ dirs d, f y * f (y + v))
        + ∑ y ∈ V, ∑ v ∈ dirs d, (f (y + v))^2 := by
    rw [energy, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  have h1 : (∑ y ∈ V, ∑ v ∈ dirs d, (f y)^2) = 2 * (d:ℝ) * ∑ y ∈ B, (f y)^2 := by
    have : ∀ y : Site d, (∑ _v ∈ dirs d, (f y)^2) = 2 * (d:ℝ) * (f y)^2 := by
      intro y
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun y _ => this y), ← Finset.mul_sum, hVB]
  have h2 : (∑ y ∈ V, ∑ v ∈ dirs d, (f (y + v))^2) = 2 * (d:ℝ) * ∑ y ∈ B, (f y)^2 := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun v hv => hshift v hv), Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast
    ring
  rw [hexp, h1, h2, hcross]
  have h3 : ∑ y ∈ B, f y * (2 * (d:ℝ) * f y - ∑ v ∈ dirs d, f (y + v))
      = 2 * (d:ℝ) * (∑ y ∈ B, (f y)^2) - ∑ y ∈ B, ∑ v ∈ dirs d, f y * f (y + v) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [mul_sub, Finset.mul_sum]
    ring
  rw [h3]
  ring

/-! ## Cauchy--Schwarz along the geodesic -/

/-- Bounds the square of the potential difference between x and p by the path length times the energy of f, via Cauchy–Schwarz along the lattice geodesic. -/
lemma value_sq_le (V : Finset (Site d)) (f : Site d → ℝ) (x p : Site d)
    (hfp : f p = 0)
    (hpath : ∀ k, k < nrm1 (p - x) → gpath p x k ∈ V) :
    (f x)^2 ≤ (nrm1 (p - x) : ℝ) * energy V f := by
  classical
  set L := nrm1 (p - x) with hL
  set δ : ℕ → ℝ := fun k => f (gpath p x k) - f (gpath p x (k+1)) with hδ
  have htel : ∑ k ∈ Finset.range L, δ k = f x - f p := by
    rw [hδ]
    rw [Finset.sum_range_sub' (fun k => f (gpath p x k)) L, gpath_zero, gpath_end]
  have hfx : f x = ∑ k ∈ Finset.range L, δ k := by rw [htel, hfp, sub_zero]
  have hcs : (f x)^2 ≤ (L : ℝ) * ∑ k ∈ Finset.range L, (δ k)^2 := by
    rw [hfx]
    have hc := sq_sum_le_card_mul_sum_sq (s := Finset.range L) (f := δ)
    simpa using hc
  have hsub : ∑ k ∈ Finset.range L, (δ k)^2 ≤ energy V f := by
    set F : Site d × Site d → ℝ := fun q => (f q.1 - f (q.1 + q.2))^2 with hF
    set Φ : ℕ → Site d × Site d := fun k => (gpath p x k, towardVec p (gpath p x k)) with hΦ
    have hδF : ∀ k ∈ Finset.range L, (δ k)^2 = F (Φ k) := by
      intro k _
      show (f (gpath p x k) - f (gpath p x (k+1)))^2
        = (f (gpath p x k) - f (gpath p x k + towardVec p (gpath p x k)))^2
      rw [gpath_succ, toward]
    have hinj : Set.InjOn Φ ((Finset.range L : Finset ℕ) : Set ℕ) := by
      intro k hk l hl hkl
      have hk' : k ≤ L := le_of_lt (Finset.mem_range.mp (Finset.mem_coe.mp hk))
      have hl' : l ≤ L := le_of_lt (Finset.mem_range.mp (Finset.mem_coe.mp hl))
      exact gpath_injOn p x hk' hl' (congrArg Prod.fst hkl)
    have himg : ((Finset.range L).image Φ) ⊆ V ×ˢ dirs d := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨k, hk, rfl⟩ := hq
      have hkL : k < L := Finset.mem_range.mp hk
      refine Finset.mem_product.mpr ⟨hpath k hkL, ?_⟩
      obtain ⟨a, ha⟩ := towardVec_isDir (gpath_ne (p := p) (x := x) hkL)
      rw [hΦ]
      simp only
      rw [ha]
      exact dirVec_mem_dirs a
    have henergy : energy V f = ∑ q ∈ V ×ˢ dirs d, F q := by
      rw [energy, Finset.sum_product]
    calc ∑ k ∈ Finset.range L, (δ k)^2
        = ∑ k ∈ Finset.range L, F (Φ k) := Finset.sum_congr rfl hδF
      _ = ∑ q ∈ (Finset.range L).image Φ, F q := (Finset.sum_image hinj).symm
      _ ≤ ∑ q ∈ V ×ˢ dirs d, F q :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun q _ _ => by positivity)
      _ = energy V f := henergy.symm
  have hE : 0 ≤ energy V f :=
    Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun v _ => sq_nonneg _
  calc (f x)^2 ≤ (L : ℝ) * ∑ k ∈ Finset.range L, (δ k)^2 := hcs
    _ ≤ (L : ℝ) * energy V f := by
        refine mul_le_mul_of_nonneg_left hsub (by positivity)

/-! ## Thomson bound -/

/-- Thomson's principle in the only form used: the effective resistance from
`x` to the complement of `insert x A` is at most twice the `ℓ¹` distance from
`x` to any point outside `insert x A`.  The unit flow along the lattice
geodesic to that point dissipates energy at most its length; the factor `2`
comes from counting each edge in both directions. -/
theorem reff_le_nrm1 (hd : 0 < d) (A : Finset (Site d)) (x p : Site d)
    (hp : p ∉ insert x A) :
    Reff A x ≤ 2 * (nrm1 (p - x) : ℝ) := by
  classical
  set B : Finset (Site d) := insert x A with hB
  have hxB : x ∈ B := Finset.mem_insert_self x A
  set ξ : B := ⟨x, hxB⟩ with hξ
  set f : Site d → ℝ := fun z => -(green B ξ z) with hfdef
  have hfnn : ∀ z, 0 ≤ f z := fun z => neg_nonneg.mpr (green_nonpos hd B ξ z)
  have hfoff : ∀ z, z ∉ B → f z = 0 := by
    intro z hz
    show -(green B ξ z) = 0
    rw [green, extendZero_of_notMem B _ hz, neg_zero]
  have hfx : f x = Reff A x := by
    show -(green B ξ x) = Reff A x
    rw [Reff_eq_neg_green A x]
  set L : ℕ := nrm1 (p - x) with hLdef
  set V : Finset (Site d) :=
    (B ∪ B.biUnion (fun z => (dirs d).image (fun v => z + v)))
      ∪ (Finset.range L).image (gpath p x) with hV
  have hBV : B ⊆ V := fun z hz => Finset.mem_union_left _ (Finset.mem_union_left _ hz)
  have hnb : ∀ z ∈ B, ∀ v ∈ dirs d, z + v ∈ V := by
    intro z hz v hv
    refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
    exact Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_image_of_mem _ hv⟩
  have hpathV : ∀ k, k < L → gpath p x k ∈ V := by
    intro k hk
    exact Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hk))
  have hterm : ∀ y ∈ B, 2*(d:ℝ)*f y - ∑ v ∈ dirs d, f (y + v) = if y = x then 1 else 0 := by
    intro y hy
    have hg := green_lap' hd B ξ y hy
    have hsum : ∑ v ∈ dirs d, f (y + v) = -∑ a : Dir d, green B ξ (y + dirVec a) := by
      rw [sum_dirs (fun v => f (y + v))]
      rw [← Finset.sum_neg_distrib]
    have hxi : (ξ : Site d) = x := rfl
    rw [hsum, hg, hxi]
    show 2*(d:ℝ)*(-(green B ξ y)) - _ = _
    by_cases hc : y = x <;> simp [hc]
  have hEid : energy V f
      = 2 * ∑ y ∈ B, f y * (2*(d:ℝ)*f y - ∑ v ∈ dirs d, f (y + v)) :=
    energy_eq B V f hfoff hBV hnb
  have hEval : energy V f = 2 * f x := by
    rw [hEid]
    congr 1
    rw [Finset.sum_congr rfl (fun y hy => by rw [hterm y hy])]
    rw [Finset.sum_congr rfl (fun y _ => show f y * (if y = x then (1:ℝ) else 0)
        = if y = x then f y else 0 by by_cases hc : y = x <;> simp [hc])]
    rw [Finset.sum_ite_eq' B x f, if_pos hxB]
  have hcs := value_sq_le V f x p (hfoff p hp) hpathV
  rw [hEval, ← hLdef] at hcs
  have hLnn : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
  nlinarith [hcs, hfnn x, hfx]

/-! ## The escape distance -/

/-- A point outside `B` at `ℓ¹` distance at most `|B|` from `x`. -/
lemma exists_far (hd : 0 < d) (B : Finset (Site d)) (x : Site d) :
    ∃ p : Site d, p ∉ B ∧ nrm1 (p - x) ≤ B.card := by
  classical
  obtain ⟨j₀⟩ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  set q : ℕ → Site d := fun k => (fun i => if i = j₀ then x i + (k:ℤ) else x i) with hq
  have hdiff : ∀ k : ℕ, nrm1 (q k - x) = k := by
    intro k
    have hc : ∀ i, (q k - x) i = if i = j₀ then (k:ℤ) else 0 := by
      intro i
      by_cases hi : i = j₀ <;> simp [hq, hi]
    rw [nrm1, Finset.sum_congr rfl (fun i _ => by rw [hc i])]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), if_pos rfl]
    rw [Finset.sum_eq_zero (fun i hi => by rw [if_neg (Finset.ne_of_mem_erase hi)]; rfl)]
    simp
  have hinj : ∀ k ∈ Finset.range (B.card + 1), ∀ l ∈ Finset.range (B.card + 1),
      q k = q l → k = l := by
    intro k _ l _ h
    have h1 : nrm1 (q k - x) = nrm1 (q l - x) := by rw [h]
    rw [hdiff, hdiff] at h1
    exact h1
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.range (B.card + 1)).image q ⊆ B := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    by_contra hzB
    have := hcon (q k) hzB
    rw [hdiff] at this
    have := Finset.mem_range.mp hk
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (fun k hk l hl h => hinj k hk l hl h),
    Finset.card_range] at hcard
  omega

open Classical in
/-- The `ℓ¹` distance from `x` to the complement of `B`. -/
noncomputable def esc (B : Finset (Site d)) (x : Site d) : ℕ :=
  sInf {L : ℕ | ∃ p : Site d, p ∉ B ∧ nrm1 (p - x) = L}

/-- Bridges the hand-rolled flow machinery to the paper's packing bound by supplying the effective-resistance estimate `Reff ≤ 2L` that replaces the Thomson's principle step. -/
lemma esc_spec (hd : 0 < d) (B : Finset (Site d)) (x : Site d) :
    ∃ p : Site d, p ∉ B ∧ nrm1 (p - x) = esc B x := by
  have hne : {L : ℕ | ∃ p : Site d, p ∉ B ∧ nrm1 (p - x) = L}.Nonempty := by
    obtain ⟨p, hp, _⟩ := exists_far hd B x
    exact ⟨nrm1 (p - x), p, hp, rfl⟩
  exact Nat.sInf_mem hne

/-- Bounds the escape probability from below by one minus the ratio of the effective resistance to twice the path length, the key step in the packing argument. -/
lemma esc_le {B : Finset (Site d)} {x p : Site d} (hp : p ∉ B) :
    esc B x ≤ nrm1 (p - x) :=
  Nat.sInf_le ⟨p, hp, rfl⟩

/-- A site whose distance from x is strictly below the escape radius of B must already lie in B, the key containment used when bounding the resistance by the path length. -/
lemma mem_of_lt_esc {B : Finset (Site d)} {x z : Site d} (h : nrm1 (z - x) < esc B x) :
    z ∈ B := by
  by_contra hz
  exact absurd (esc_le (x := x) hz) (by omega)

/-- Bounds the exit probability of the walk from the box by the number of sites it contains, a trivial counting input to the packing argument. -/
lemma esc_le_card (hd : 0 < d) (B : Finset (Site d)) (x : Site d) : esc B x ≤ B.card := by
  obtain ⟨p, hp, hple⟩ := exists_far hd B x
  exact le_trans (esc_le hp) hple

/-! ## Boxes -/

/-- The translate by `c` of the box `{z : 0 ≤ z i ≤ q}`. -/
def qbox (c : Site d) (q : ℕ) : Finset (Site d) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.Icc (0:ℤ) (q:ℤ))).image (fun z => c + z)

/-- Counts the sites in a box of radius q, the basic volume input to the packing bound. -/
lemma card_qbox (c : Site d) (q : ℕ) : (qbox c q).card = (q+1)^d := by
  rw [qbox, Finset.card_image_of_injective _ (add_right_injective c),
    Fintype.card_piFinset]
  have : ∀ _j : Fin d, (Finset.Icc (0:ℤ) (q:ℤ)).card = q + 1 := by
    intro _
    rw [Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl (fun j _ => this j), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- Bounds the ℓ¹ distance of a site from the center of a box by the box's radius times the dimension. -/
lemma nrm1_le_of_mem_qbox {c z : Site d} {q : ℕ} (h : z ∈ qbox c q) : nrm1 (z - c) ≤ d * q := by
  rw [qbox, Finset.mem_image] at h
  obtain ⟨w, hw, rfl⟩ := h
  rw [Fintype.mem_piFinset] at hw
  have hz : ∀ i, (c + w - c) i = w i := by intro i; simp
  rw [nrm1, Finset.sum_congr rfl (fun i _ => by rw [hz i])]
  have hb : ∀ i : Fin d, (w i).natAbs ≤ q := by
    intro i
    have := Finset.mem_Icc.mp (hw i)
    omega
  calc ∑ i : Fin d, (w i).natAbs ≤ ∑ _i : Fin d, q := Finset.sum_le_sum fun i _ => hb i
    _ = d * q := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-! ## The packing count -/

/-- Counts the sites whose escape radius reaches r, providing the packing bound ingredient that the resistance estimate converts into the linear-in-r lower bound on the number of boxes. -/
lemma packing_count {M : ℕ} (x : Fin M → Site d) (hinj : Function.Injective x)
    (r : ℕ) (hr : 1 ≤ r) :
    (Finset.univ.filter (fun i : Fin M => r ≤ esc (pref x ((i:ℕ)+1)) (x i))).card
      * (((r-1)/(2*d)) + 1)^d ≤ M := by
  classical
  set q : ℕ := (r-1)/(2*d) with hq
  set S : Finset (Fin M) :=
    Finset.univ.filter (fun i : Fin M => r ≤ esc (pref x ((i:ℕ)+1)) (x i)) with hS
  have hqd : q * (2*d) = d * q + d * q := by ring
  have hdq : d * q + d * q ≤ r - 1 := by
    rw [← hqd, hq]
    exact Nat.div_mul_le_self _ _
  have hdqr : d * q < r := by omega
  have hsep : ∀ i ∈ S, ∀ j : Fin M, (i:ℕ) < (j:ℕ) → r ≤ nrm1 (x j - x i) := by
    intro i hi j hij
    have hnot : x j ∉ pref x ((i:ℕ)+1) := by
      simp only [pref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨l, hl, hxl⟩
      have hlj : l = j := hinj hxl
      rw [hlj] at hl
      omega
    have h1 := esc_le (x := x i) hnot
    have h2 := (Finset.mem_filter.mp hi).2
    omega
  have hsubs : ∀ i ∈ S, qbox (x i) q ⊆ pref x M := by
    intro i hi z hz
    have hle : nrm1 (z - x i) ≤ d * q := nrm1_le_of_mem_qbox hz
    have h2 := (Finset.mem_filter.mp hi).2
    have hmem : z ∈ pref x ((i:ℕ)+1) := mem_of_lt_esc (x := x i) (by omega)
    exact pref_mono x (by omega) hmem
  have hdisj : (S : Set (Fin M)).PairwiseDisjoint (fun i => qbox (x i) q) := by
    have hkey : ∀ i ∈ S, ∀ j : Fin M, (i:ℕ) < (j:ℕ) →
        Disjoint (qbox (x i) q) (qbox (x j) q) := by
      intro i hi j hij
      rw [Finset.disjoint_left]
      intro w hwi hwj
      have h1 : nrm1 (w - x i) ≤ d * q := nrm1_le_of_mem_qbox hwi
      have h2 : nrm1 (x j - w) ≤ d * q := by
        rw [nrm1_sub_comm]
        exact nrm1_le_of_mem_qbox hwj
      have h3 : nrm1 (x j - x i) ≤ nrm1 (x j - w) + nrm1 (w - x i) := by
        have hsplit : x j - x i = (x j - w) + (w - x i) := by abel
        rw [hsplit]
        exact nrm1_add_le _ _
      have h4 := hsep i hi j hij
      omega
    intro i hi j hj hne
    have hne' : (i:ℕ) ≠ (j:ℕ) := fun hc => hne (Fin.ext hc)
    rcases Nat.lt_or_ge (i:ℕ) (j:ℕ) with h | h
    · exact hkey i (Finset.mem_coe.mp hi) j h
    · exact (hkey j (Finset.mem_coe.mp hj) i (by omega)).symm
  have hcardU : (S.biUnion (fun i => qbox (x i) q)).card = S.card * (q+1)^d := by
    rw [Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl (fun i _ => card_qbox (x i) q), Finset.sum_const, smul_eq_mul]
  have hsubU : S.biUnion (fun i => qbox (x i) q) ⊆ pref x M := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp hz
    exact hsubs i hi hzi
  have := Finset.card_le_card hsubU
  rw [hcardU, pref_card x hinj] at this
  exact this

/-! ## The resistance packing bound -/

/-- Delivers the resistance packing bound by producing a uniform constant so that any finite set of distinct sites has bounded total weight. -/
theorem resistance_packing_aux (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → ∀ x : Fin M → Site d, Function.Injective x →
      ∑ i : Fin M, Reff ((Finset.Iio i).image x) (x i) ≤ C * (M : ℝ) := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  refine ⟨2 * (1 + ((2*(d:ℝ))^d)), by positivity, ?_⟩
  intro M hM x hinj
  set ρ : Fin M → ℕ := fun i => esc (pref x ((i:ℕ)+1)) (x i) with hρ
  -- Thomson
  have hReff : ∀ i : Fin M,
      Reff ((Finset.Iio i).image x) (x i) ≤ 2 * (ρ i : ℝ) := by
    intro i
    rw [pref_Iio]
    obtain ⟨p, hp, hpe⟩ := esc_spec hd0 (pref x ((i:ℕ)+1)) (x i)
    have hp' : p ∉ insert (x i) (pref x (i:ℕ)) := by rw [pref_succ x i]; exact hp
    have hb := reff_le_nrm1 hd0 (pref x (i:ℕ)) (x i) p hp'
    rw [hpe] at hb
    exact hb
  -- ρ i ≤ M
  have hρle : ∀ i : Fin M, ρ i ≤ M := by
    intro i
    have h1 : esc (pref x ((i:ℕ)+1)) (x i) ≤ (pref x ((i:ℕ)+1)).card :=
      esc_le_card hd0 _ _
    have h2 : (pref x ((i:ℕ)+1)).card ≤ (pref x M).card :=
      Finset.card_le_card (pref_mono x (by omega))
    rw [pref_card x hinj] at h2
    exact le_trans h1 h2
  set Nn : ℕ → ℕ :=
    fun r => (Finset.univ.filter (fun i : Fin M => r < ρ i)).card with hNdef
  -- layer cake
  have hlayer : ∑ i : Fin M, ρ i = ∑ r ∈ Finset.range M, Nn r := by
    have hrow : ∀ i : Fin M, ρ i = ∑ r ∈ Finset.range M, (if r < ρ i then 1 else 0) := by
      intro i
      rw [← Finset.sum_filter]
      have hf : (Finset.range M).filter (fun r => r < ρ i) = Finset.range (ρ i) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_range]
        have := hρle i
        omega
      rw [hf, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hNdef]
    simp only
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  -- the packing estimate
  have hNbound : ∀ r : ℕ, Nn r * (r+1)^2 ≤ M * (2*d)^d := by
    intro r
    have hpc := packing_count x hinj (r+1) (by omega)
    have hfe : (Finset.univ.filter (fun i : Fin M => r + 1 ≤ esc (pref x ((i:ℕ)+1)) (x i)))
        = (Finset.univ.filter (fun i : Fin M => r < ρ i)) := by
      apply Finset.filter_congr
      intro i _
      simp only [hρ]
      constructor <;> intro h <;> omega
    rw [hfe] at hpc
    have hq : r < (r / (2*d) + 1) * (2*d) := by
      have h1 : (2*d) * (r / (2*d)) + r % (2*d) = r := Nat.div_add_mod r (2*d)
      have h2 : r % (2*d) < 2*d := Nat.mod_lt _ (by omega)
      have h3 : (r / (2*d) + 1) * (2*d) = (2*d) * (r / (2*d)) + (2*d) := by ring
      omega
    have hpow : (r+1)^d ≤ (r / (2*d) + 1)^d * (2*d)^d := by
      rw [← Nat.mul_pow]
      exact Nat.pow_le_pow_left (by omega) d
    have hsq : (r+1)^2 ≤ (r+1)^d := Nat.pow_le_pow_right (by omega) hd
    calc Nn r * (r+1)^2 ≤ Nn r * ((r / (2*d) + 1)^d * (2*d)^d) := by
          exact Nat.mul_le_mul_left _ (le_trans hsq hpow)
      _ = (Nn r * ((r+1-1) / (2*d) + 1)^d) * (2*d)^d := by
          simp only [Nat.add_sub_cancel]
          ring
      _ ≤ M * (2*d)^d := Nat.mul_le_mul_right _ hpc
  -- sum the layers in ℝ
  have hsum : (∑ r ∈ Finset.range M, (Nn r : ℝ)) ≤ (1 + (2*(d:ℝ))^d) * M := by
    obtain ⟨M', rfl⟩ : ∃ M' : ℕ, M = M' + 1 := ⟨M - 1, by omega⟩
    rw [Finset.sum_range_succ' (fun r => (Nn r : ℝ)) M']
    have hN0 : (Nn 0 : ℝ) ≤ ((M' + 1 : ℕ) : ℝ) := by
      have : Nn 0 ≤ M' + 1 := by
        rw [hNdef]
        simpa using Finset.card_filter_le (Finset.univ : Finset (Fin (M'+1))) _
      exact_mod_cast this
    have hstep : ∀ r ∈ Finset.range M', (Nn (r+1) : ℝ)
        ≤ (((M':ℝ)+1) * (2*(d:ℝ))^d) * (1/((r:ℝ)+1) - 1/((r:ℝ)+2)) := by
      intro r _
      have hb := hNbound (r+1)
      have hbR : (Nn (r+1) : ℝ) * ((r:ℝ)+2)^2 ≤ ((M':ℝ)+1) * (2*(d:ℝ))^d := by
        have : ((Nn (r+1) * (r+1+1)^2 : ℕ) : ℝ) ≤ (((M'+1) * (2*d)^d : ℕ) : ℝ) := by
          exact_mod_cast hb
        push_cast at this
        nlinarith [this]
      have hid : (1/((r:ℝ)+1) - 1/((r:ℝ)+2)) = 1/(((r:ℝ)+1)*((r:ℝ)+2)) := by
        field_simp
        ring
      have hle : ((r:ℝ)+1)*((r:ℝ)+2) ≤ ((r:ℝ)+2)^2 := by nlinarith [sq_nonneg ((r:ℝ)+1)]
      have hNnn : (0:ℝ) ≤ (Nn (r+1) : ℝ) := Nat.cast_nonneg _
      rw [hid, mul_one_div, le_div_iff₀ (by positivity)]
      nlinarith [hbR, hle, hNnn]
    have htele : ∑ r ∈ Finset.range M', (1/((r:ℝ)+1) - 1/((r:ℝ)+2)) ≤ 1 := by
      have := Finset.sum_range_sub' (fun r : ℕ => 1/((r:ℝ)+1)) M'
      simp only at this
      have hpos : (0:ℝ) < 1/((M':ℝ)+1) := by positivity
      have heq : ∑ r ∈ Finset.range M', (1/((r:ℝ)+1) - 1/(((r:ℝ)+1)+1))
          = 1/((0:ℝ)+1) - 1/((M':ℝ)+1) := by
        exact_mod_cast this
      have hcast : ∑ r ∈ Finset.range M', (1/((r:ℝ)+1) - 1/((r:ℝ)+2))
          = ∑ r ∈ Finset.range M', (1/((r:ℝ)+1) - 1/(((r:ℝ)+1)+1)) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        norm_num
        ring
      rw [hcast, heq]
      norm_num
      positivity
    have hstepsum : ∑ r ∈ Finset.range M', (Nn (r+1) : ℝ)
        ≤ (((M':ℝ)+1) * (2*(d:ℝ))^d) * ∑ r ∈ Finset.range M', (1/((r:ℝ)+1) - 1/((r:ℝ)+2)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hstep
    have hfac : (0:ℝ) ≤ ((M':ℝ)+1) * (2*(d:ℝ))^d := by positivity
    have : (((M':ℝ)+1) * (2*(d:ℝ))^d)
        * ∑ r ∈ Finset.range M', (1/((r:ℝ)+1) - 1/((r:ℝ)+2))
        ≤ ((M':ℝ)+1) * (2*(d:ℝ))^d := by
      nlinarith [htele, hfac]
    push_cast at hN0 ⊢
    linarith [hstepsum, this, hN0]
  -- assemble
  calc ∑ i : Fin M, Reff ((Finset.Iio i).image x) (x i)
      ≤ ∑ i : Fin M, 2 * (ρ i : ℝ) := Finset.sum_le_sum fun i _ => hReff i
    _ = 2 * ((∑ i : Fin M, ρ i : ℕ) : ℝ) := by
        rw [← Finset.mul_sum]
        norm_cast
    _ = 2 * ((∑ r ∈ Finset.range M, Nn r : ℕ) : ℝ) := by rw [hlayer]
    _ = 2 * ∑ r ∈ Finset.range M, (Nn r : ℝ) := by push_cast; ring
    _ ≤ 2 * ((1 + (2*(d:ℝ))^d) * M) := by linarith [hsum]
    _ = 2 * (1 + (2*(d:ℝ))^d) * (M:ℝ) := by ring

end ORRW.Support
