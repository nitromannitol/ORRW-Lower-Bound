/-
Supporting lemmas for the exit time bounds of Bou-Rabee--Peres, Section 2,
`orrw.tex` (label `lem:max-exit`).

Nothing here is frozen.  This file proves the third assertion of that lemma,
`T(A) ≤ C|A|^{1+2/d}`, and `ORRW/Support/ExitTime.lean` deduces the other two
from it.

The paper proves `lem:max-exit` through Nash, Faber--Krahn and Telcs
Proposition 3.5, none of which is in Mathlib.  The route taken here replaces
all three by one elementary comparison, which works in every dimension `d ≥ 1`
and needs no Green function:

  Let `Q` be the box `{0,…,q}^d` of side `q+1 ≥ (2|A|)^{1/d}`, so that
  `|Q| ≥ 2|A|`, and let `u_Q(x) := |Q|^{-1} ∑_{w ∈ Q} u_A(x+w)` be the box
  average of the mean exit time.  Two estimates pull in opposite directions:

  * The average is small: `u_Q ≤ T(A)/|Q|` everywhere, because `u_A ≥ 0` and
    its total mass is `T(A)`.  Cauchy--Schwarz turns this into
    `⟨u_A, u_Q⟩ ≤ |A| ‖u_A‖_2^2 / |Q| ≤ ‖u_A‖_2^2/2`, so the average cannot
    account for more than half of `‖u_A‖_2^2`.

  * Averaging cannot move `u_A` far: `‖u_A - u_Q‖_2^2 ≤ (dq)^2 ‖∇u_A‖_2^2`.
    This is `poincare` below.  It telescopes `u_A(x) - u_A(x+w)` along the
    coordinate geodesic of `ORRW/Support/Thomson.lean`, which has at most `dq`
    steps for `w ∈ Q`, and applies Cauchy--Schwarz twice, once along the
    geodesic and once over `w ∈ Q`.  The one structural input is that the
    `k`-th step of the geodesic from `x` to `x+w` is a unit vector depending
    only on `w` and `k`, so translating in `x` reindexes a single directional
    slice of the energy.

  Together `‖u_A‖_2 ≤ 2dq‖∇u_A‖_2`.  Since `‖∇u_A‖_2^2 = ⟨u_A, -Δ_A u_A⟩
  = T(A)` and `T(A) ≤ |A|^{1/2}‖u_A‖_2`, this reads `T(A) ≤ 8d^2q^2|A|`, and
  `q ≍ |A|^{1/d}` gives `T(A) ≤ 72d^2|A|^{1+2/d}`.

The Dirichlet energy is the one already defined in `ORRW/Support/Thomson.lean`,
where each undirected edge is counted once in each direction, so
`energy V u_A = 2T(A)` rather than `T(A)`.
-/
import Mathlib
import ORRW.Basic
import ORRW.Lattice
import ORRW.Support.Insertion
import ORRW.Support.Thomson

open Finset

namespace ORRW.Support

variable {d : ℕ}

/-! ## Elementary facts about `u` and `T` -/

/-- The expected exit time of a walk from a set vanishes off the set, since the walk starts outside and exits immediately. -/
lemma u_off (A : Finset (Site d)) {z : Site d} (hz : z ∉ A) : u A z = 0 :=
  extendZero_of_notMem A _ hz

/-- The mean exit time is nonnegative, so the total charge T(A) is a nonnegative quantity. -/
lemma T_nonneg (hd : 0 < d) (A : Finset (Site d)) : 0 ≤ T A :=
  Finset.sum_nonneg fun z _ => u_nonneg hd A z

/-- The sum of `u_A` over any finite set is at most `T(A)`, since `u_A` is
nonnegative and vanishes off `A`. -/
lemma sum_u_le_T (hd : 0 < d) (A S : Finset (Site d)) :
    ∑ z ∈ S, u A z ≤ T A := by
  classical
  have hsplit : ∑ z ∈ S ∩ A, u A z + ∑ z ∈ S \ A, u A z = ∑ z ∈ S, u A z :=
    Finset.sum_inter_add_sum_diff S A (u A)
  have hzero : ∑ z ∈ S \ A, u A z = 0 :=
    Finset.sum_eq_zero fun z hz => u_off A (Finset.mem_sdiff.mp hz).2
  have hle : ∑ z ∈ S ∩ A, u A z ≤ ∑ z ∈ A, u A z :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun z _ _ => u_nonneg hd A z)
  rw [T]
  linarith

/-! ## The Dirichlet energy of the mean exit time -/

/-- A finite set containing `Y`, `A`, and every neighbour of a point of `A`. -/
def bigSet (Y A : Finset (Site d)) : Finset (Site d) :=
  (Y ∪ A) ∪ A.biUnion (fun z => (dirs d).image (fun v => z + v))

/-- Every site of Y already belongs to the big set built from Y and A, via the left-hand union inclusions. -/
lemma subset_bigSet_left (Y A : Finset (Site d)) : Y ⊆ bigSet Y A :=
  fun _ hz => Finset.mem_union_left _ (Finset.mem_union_left _ hz)

/-- Every site of A lies in the middle layer of the enlarged set, a bookkeeping step used when comparing the walk's behaviour on A with its behaviour on the surrounding box. -/
lemma subset_bigSet_right (Y A : Finset (Site d)) : A ⊆ bigSet Y A :=
  fun _ hz => Finset.mem_union_left _ (Finset.mem_union_right _ hz)

/-- A site of the range adjacent to a charged vertex belongs to the big set used in the exit time comparison. -/
lemma nbr_mem_bigSet (Y A : Finset (Site d)) {z : Site d} (hz : z ∈ A) {v : Site d}
    (hv : v ∈ dirs d) : z + v ∈ bigSet Y A :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_image_of_mem _ hv⟩)

/-- `⟨u_A, -Δ_A u_A⟩ = T(A)`, in the doubled normalization of `energy`. -/
lemma energy_u (hd : 0 < d) (A V : Finset (Site d)) (hAV : A ⊆ V)
    (hnb : ∀ z ∈ A, ∀ v ∈ dirs d, z + v ∈ V) :
    energy V (u A) = 2 * T A := by
  rw [energy_eq A V (u A) (fun z hz => u_off A hz) hAV hnb, T]
  congr 1
  refine Finset.sum_congr rfl fun y hy => ?_
  have hlap : ∑ v ∈ dirs d, u A (y + v) = 2 * (d:ℝ) * u A y - 1 := by
    rw [sum_dirs (fun v => u A (y + v))]
    exact u_lap hd A y hy
  rw [hlap]
  ring

/-- One directional slice of the energy of `u_A`, over an arbitrary finite set
of base points, is at most `2T(A)`. -/
lemma sum_sq_dir_le (hd : 0 < d) (A : Finset (Site d)) {v : Site d} (hv : v ∈ dirs d)
    (Y : Finset (Site d)) :
    ∑ y ∈ Y, (u A y - u A (y + v)) ^ 2 ≤ 2 * T A := by
  classical
  set V := bigSet Y A with hV
  have h1 : ∑ y ∈ Y, (u A y - u A (y + v)) ^ 2 ≤ ∑ y ∈ V, (u A y - u A (y + v)) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (subset_bigSet_left Y A)
      (fun _ _ _ => sq_nonneg _)
  have h2 : ∑ y ∈ V, (u A y - u A (y + v)) ^ 2 ≤ energy V (u A) := by
    rw [energy]
    refine Finset.sum_le_sum fun y _ => ?_
    exact Finset.single_le_sum (f := fun w => (u A y - u A (y + w)) ^ 2)
      (fun w _ => sq_nonneg _) hv
  have h3 : energy V (u A) = 2 * T A :=
    energy_u hd A V (subset_bigSet_right Y A) (fun z hz v hv => nbr_mem_bigSet Y A hz hv)
  linarith

/-! ## The coordinate geodesic from the origin -/

/-- The lattice geodesic of `ORRW/Support/Thomson.lean` run from the origin.
Its `k`-th step depends only on `w` and `k`, so the path from `x` to `x+w` is
the translate `x + seg w k`. -/
noncomputable def seg (w : Site d) (k : ℕ) : Site d := gpath w 0 k

@[simp] lemma seg_zero (w : Site d) : seg w 0 = 0 := rfl

/-- Walking a site's own length along its normalized direction returns to the site itself, the trivial segment identity used to telescope displacements in the Poincaré comparison. -/
lemma seg_len (w : Site d) : seg w (nrm1 w) = w := by
  have h := gpath_end w (0 : Site d)
  rwa [sub_zero] at h

/-- Provides the individual step along a coordinate geodesic from a site toward the origin, used to telescope the walk's displacement when bounding exit times. -/
lemma seg_step (w : Site d) {k : ℕ} (hk : k < nrm1 w) :
    ∃ v ∈ dirs d, seg w (k + 1) = seg w k + v := by
  have hne : gpath w 0 k ≠ w := gpath_ne (p := w) (x := (0 : Site d)) (by rwa [sub_zero])
  obtain ⟨a, ha⟩ := towardVec_isDir hne
  refine ⟨dirVec a, dirVec_mem_dirs a, ?_⟩
  rw [seg, seg, gpath_succ, toward, ha]

/-- Telescoping `u_A(x) - u_A(x+w)` along the geodesic and applying
Cauchy--Schwarz.  Each of the `nrm1 w` steps contributes a single directional
slice of the energy, bounded by `sum_sq_dir_le`. -/
lemma sum_sq_shift_le (hd : 0 < d) (A S : Finset (Site d)) (w : Site d) :
    ∑ x ∈ S, (u A x - u A (x + w)) ^ 2 ≤ (nrm1 w : ℝ) ^ 2 * (2 * T A) := by
  classical
  set L := nrm1 w with hL
  have hxbound : ∀ x : Site d, (u A x - u A (x + w)) ^ 2
      ≤ (L : ℝ) * ∑ k ∈ Finset.range L, (u A (x + seg w k) - u A (x + seg w (k+1))) ^ 2 := by
    intro x
    have htel : ∑ k ∈ Finset.range L, (u A (x + seg w k) - u A (x + seg w (k+1)))
        = u A (x + seg w 0) - u A (x + seg w L) :=
      Finset.sum_range_sub' (fun k => u A (x + seg w k)) L
    have h0 : x + seg w 0 = x := by rw [seg_zero, add_zero]
    have hLw : x + seg w L = x + w := by rw [hL, seg_len]
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range L)
      (f := fun k => u A (x + seg w k) - u A (x + seg w (k+1)))
    rw [Finset.card_range] at hcs
    rw [htel, h0, hLw] at hcs
    exact hcs
  have hstep : ∀ k ∈ Finset.range L,
      ∑ x ∈ S, (u A (x + seg w k) - u A (x + seg w (k+1))) ^ 2 ≤ 2 * T A := by
    intro k hk
    obtain ⟨v, hv, hvk⟩ := seg_step w (Finset.mem_range.mp hk)
    have himg : ∑ x ∈ S, (u A (x + seg w k) - u A (x + seg w (k+1))) ^ 2
        = ∑ y ∈ S.image (fun x => x + seg w k), (u A y - u A (y + v)) ^ 2 := by
      rw [Finset.sum_image (fun a _ b _ hab => add_right_cancel hab)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hvk, ← add_assoc]
    rw [himg]
    exact sum_sq_dir_le hd A hv _
  have hTnn : 0 ≤ 2 * T A := by have := T_nonneg hd A; linarith
  calc ∑ x ∈ S, (u A x - u A (x + w)) ^ 2
      ≤ ∑ x ∈ S, ((L : ℝ) * ∑ k ∈ Finset.range L,
          (u A (x + seg w k) - u A (x + seg w (k+1))) ^ 2) :=
        Finset.sum_le_sum fun x _ => hxbound x
    _ = (L : ℝ) * ∑ k ∈ Finset.range L, ∑ x ∈ S,
          (u A (x + seg w k) - u A (x + seg w (k+1))) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (L : ℝ) * ∑ _k ∈ Finset.range L, (2 * T A) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) (by positivity)
    _ = (L : ℝ) ^ 2 * (2 * T A) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-! ## The box average -/

/-- The box `{0,…,q}^d` of side `q+1`, as a set of shift vectors. -/
noncomputable def shiftBox (d q : ℕ) : Finset (Site d) := qbox (0 : Site d) q

/-- The shifted box used to average the exit-time potential has exactly the cardinality of the side-length box, matching the |Q| ≥ 2|A| requirement of the comparison argument. -/
lemma card_shiftBox (d q : ℕ) : (shiftBox d q).card = (q+1)^d := card_qbox 0 q

/-- Bounds the ℓ¹ norm of any site in the shifted box by d·q, which is the diameter estimate feeding into the Poincaré comparison between the mean exit time and its box average. -/
lemma nrm1_le_of_mem_shiftBox {q : ℕ} {w : Site d} (hw : w ∈ shiftBox d q) : nrm1 w ≤ d * q := by
  have h := nrm1_le_of_mem_qbox hw
  rwa [sub_zero] at h

/-- The box average of the mean exit time. -/
noncomputable def uAvg (A : Finset (Site d)) (q : ℕ) (x : Site d) : ℝ :=
  (∑ w ∈ shiftBox d q, u A (x + w)) / (((q+1)^d : ℕ) : ℝ)

/-- Bounds the box average of the mean exit time by T(A)/|Q|, the smallness half of the comparison argument driving the exit time estimate. -/
lemma sum_box_le_T (hd : 0 < d) (A : Finset (Site d)) (q : ℕ) (x : Site d) :
    ∑ w ∈ shiftBox d q, u A (x + w) ≤ T A := by
  classical
  have himg : ∑ z ∈ (shiftBox d q).image (fun w => x + w), u A z
      = ∑ w ∈ shiftBox d q, u A (x + w) :=
    Finset.sum_image (fun a _ b _ hab => add_right_injective x hab)
  rw [← himg]
  exact sum_u_le_T hd A _

/-- Upper-bounds the box average of the mean exit time by the total exit time divided by the box size, the smallness half of the comparison argument. -/
lemma uAvg_le (hd : 0 < d) (A : Finset (Site d)) (q : ℕ) (x : Site d) :
    uAvg A q x ≤ T A / (((q+1)^d : ℕ) : ℝ) := by
  have hn : (0:ℝ) ≤ (((q+1)^d : ℕ) : ℝ) := by positivity
  exact div_le_div_of_nonneg_right (sum_box_le_T hd A q x) hn

/-- Discrete Poincaré inequality: replacing `u_A` by its average over a box of
side `q+1` costs at most `(dq)^2` times the Dirichlet energy. -/
lemma poincare (hd : 0 < d) (A : Finset (Site d)) (q : ℕ) :
    ∑ x ∈ A, (u A x - uAvg A q x) ^ 2 ≤ ((d * q : ℕ) : ℝ) ^ 2 * (2 * T A) := by
  classical
  set n : ℝ := (((q+1)^d : ℕ) : ℝ) with hn
  have hnpos : (0:ℝ) < n := by rw [hn]; positivity
  have hcard : ((shiftBox d q).card : ℝ) = n := by rw [card_shiftBox, hn]
  have hTnn : (0:ℝ) ≤ 2 * T A := by have := T_nonneg hd A; linarith
  have hjensen : ∀ x : Site d, (u A x - uAvg A q x) ^ 2
      ≤ (∑ w ∈ shiftBox d q, (u A x - u A (x + w)) ^ 2) / n := by
    intro x
    have hsum : ∑ w ∈ shiftBox d q, (u A x - u A (x + w))
        = n * u A x - ∑ w ∈ shiftBox d q, u A (x + w) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    have hcs := sq_sum_le_card_mul_sum_sq (s := shiftBox d q) (f := fun w => u A x - u A (x + w))
    rw [hcard, hsum] at hcs
    have hrw : u A x - uAvg A q x = (n * u A x - ∑ w ∈ shiftBox d q, u A (x + w)) / n := by
      rw [uAvg, ← hn]
      field_simp
    rw [hrw, div_pow, div_le_div_iff₀ (by positivity) hnpos]
    nlinarith [hcs, hnpos]
  calc ∑ x ∈ A, (u A x - uAvg A q x) ^ 2
      ≤ ∑ x ∈ A, (∑ w ∈ shiftBox d q, (u A x - u A (x + w)) ^ 2) / n :=
        Finset.sum_le_sum fun x _ => hjensen x
    _ = (∑ w ∈ shiftBox d q, ∑ x ∈ A, (u A x - u A (x + w)) ^ 2) / n := by
        rw [← Finset.sum_div, Finset.sum_comm]
    _ ≤ (∑ _w ∈ shiftBox d q, ((d * q : ℕ) : ℝ) ^ 2 * (2 * T A)) / n := by
        refine div_le_div_of_nonneg_right ?_ (le_of_lt hnpos)
        refine Finset.sum_le_sum fun w hw => ?_
        refine le_trans (sum_sq_shift_le hd A A w) ?_
        have h1 : ((nrm1 w : ℕ) : ℝ) ≤ ((d * q : ℕ) : ℝ) := by
          exact_mod_cast nrm1_le_of_mem_shiftBox hw
        have h2 : (0:ℝ) ≤ ((nrm1 w : ℕ) : ℝ) := by positivity
        gcongr
    _ = ((d * q : ℕ) : ℝ) ^ 2 * (2 * T A) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        field_simp

/-! ## The total mass bound -/

/-- If `A` occupies at most half of a box of side `q+1`, its total mass is at
most `8(dq)^2|A|`. -/
lemma T_le_of_box (hd : 0 < d) (A : Finset (Site d)) (q : ℕ)
    (hq : 2 * A.card ≤ (q+1)^d) :
    T A ≤ 8 * ((d * q : ℕ) : ℝ) ^ 2 * (A.card : ℝ) := by
  classical
  set n : ℝ := (((q+1)^d : ℕ) : ℝ) with hn
  set m : ℝ := (A.card : ℝ) with hm
  set S2 : ℝ := ∑ x ∈ A, (u A x) ^ 2 with hS2
  set D2 : ℝ := ∑ x ∈ A, (u A x - uAvg A q x) ^ 2 with hD2
  have hnpos : (0:ℝ) < n := by rw [hn]; positivity
  have hmnn : (0:ℝ) ≤ m := by rw [hm]; positivity
  have hTnn : (0:ℝ) ≤ T A := T_nonneg hd A
  have hS2nn : (0:ℝ) ≤ S2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD2nn : (0:ℝ) ≤ D2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2mn : 2 * m ≤ n := by rw [hm, hn]; exact_mod_cast hq
  have hCS1 : (T A) ^ 2 ≤ m * S2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := A) (f := u A)
    rw [T, hm, hS2]
    exact h
  have hAvg : ∑ x ∈ A, u A x * uAvg A q x ≤ (T A) ^ 2 / n := by
    have hstep : ∀ x ∈ A, u A x * uAvg A q x ≤ u A x * (T A / n) := fun x _ =>
      mul_le_mul_of_nonneg_left (uAvg_le hd A q x) (u_nonneg hd A x)
    calc ∑ x ∈ A, u A x * uAvg A q x ≤ ∑ x ∈ A, u A x * (T A / n) :=
          Finset.sum_le_sum hstep
      _ = (T A) * (T A / n) := by rw [← Finset.sum_mul, ← T]
      _ = (T A) ^ 2 / n := by ring
  have hCS2 : (∑ x ∈ A, u A x * (u A x - uAvg A q x)) ^ 2 ≤ S2 * D2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq A (u A) (fun x => u A x - uAvg A q x)
    rw [hS2, hD2]
    exact h
  have hsplit : ∑ x ∈ A, u A x * (u A x - uAvg A q x)
      = S2 - ∑ x ∈ A, u A x * uAvg A q x := by
    rw [hS2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hPoin : D2 ≤ ((d * q : ℕ) : ℝ) ^ 2 * (2 * T A) := poincare hd A q
  rcases eq_or_lt_of_le hTnn with hT0 | hTpos
  · rw [← hT0]
    positivity
  · have hS2pos : (0:ℝ) < S2 := by nlinarith [hCS1, hTpos, hmnn]
    have hmpos : (0:ℝ) < m := by nlinarith [hCS1, hTpos, hS2pos]
    have hhalf : ∑ x ∈ A, u A x * uAvg A q x ≤ S2 / 2 := by
      have h1 : (T A) ^ 2 / n ≤ m * S2 / n :=
        div_le_div_of_nonneg_right hCS1 (le_of_lt hnpos)
      have h2 : m * S2 / n ≤ S2 / 2 := by
        rw [div_le_div_iff₀ hnpos (by norm_num)]
        nlinarith [hS2nn, h2mn]
      linarith
    have hXge : S2 / 2 ≤ ∑ x ∈ A, u A x * (u A x - uAvg A q x) := by
      rw [hsplit]; linarith
    have hXsq : (S2 / 2) ^ 2 ≤ S2 * D2 := by nlinarith [hCS2, hXge, hS2pos]
    have hS2le : S2 ≤ 4 * D2 := by nlinarith [hXsq, hS2pos]
    have hS2le' : S2 ≤ 8 * ((d * q : ℕ) : ℝ) ^ 2 * (T A) := by nlinarith [hS2le, hPoin]
    nlinarith [hCS1, hS2le', hTpos, hmpos]

/-- The total mass bound `T(A) ≤ C|A|^{1+2/d}`, the third assertion of
`lem:max-exit`. -/
theorem T_bound (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Finset (Site d),
      T A ≤ C * (A.card : ℝ) ^ (1 + (2:ℝ) / (d:ℝ)) := by
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  refine ⟨72 * (d:ℝ) ^ 2, by positivity, fun A => ?_⟩
  rcases Nat.eq_zero_or_pos A.card with hm0 | hm1
  · have hA : A = ∅ := Finset.card_eq_zero.mp hm0
    rw [hA, T]
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero]
    rw [Real.zero_rpow (by positivity)]
    norm_num
  · set m : ℝ := (A.card : ℝ) with hm
    have hm1R : (1:ℝ) ≤ m := by rw [hm]; exact_mod_cast hm1
    have hmpos : (0:ℝ) < m := lt_of_lt_of_le one_pos hm1R
    set q : ℕ := ⌈(2 * m) ^ ((d:ℝ)⁻¹)⌉₊ with hqdef
    have h2m : (0:ℝ) ≤ 2 * m := by positivity
    have hpow : ((2 * m) ^ ((d:ℝ)⁻¹)) ^ d = 2 * m :=
      Real.rpow_inv_natCast_pow h2m (by omega)
    have hqge : (2 * m) ^ ((d:ℝ)⁻¹) ≤ (q:ℝ) := Nat.le_ceil _
    have hbase : (0:ℝ) ≤ (2 * m) ^ ((d:ℝ)⁻¹) := Real.rpow_nonneg h2m _
    have hqR : 2 * m ≤ ((q:ℝ) + 1) ^ d := by
      calc 2 * m = ((2 * m) ^ ((d:ℝ)⁻¹)) ^ d := hpow.symm
        _ ≤ ((q:ℝ) + 1) ^ d := by
            refine pow_le_pow_left₀ hbase ?_ d
            linarith
    have hq : 2 * A.card ≤ (q + 1) ^ d := by
      have hcast : ((2 * A.card : ℕ) : ℝ) ≤ (((q+1)^d : ℕ) : ℝ) := by
        push_cast
        rw [hm] at hqR
        linarith
      exact_mod_cast hcast
    have hmd : (1:ℝ) ≤ m ^ ((d:ℝ)⁻¹) := Real.one_le_rpow hm1R (by positivity)
    have hsplit : (2 * m) ^ ((d:ℝ)⁻¹) = (2:ℝ) ^ ((d:ℝ)⁻¹) * m ^ ((d:ℝ)⁻¹) :=
      Real.mul_rpow (by norm_num) (le_of_lt hmpos)
    have h2d : (2:ℝ) ^ ((d:ℝ)⁻¹) ≤ 2 := by
      have h1 : (2:ℝ) ^ ((d:ℝ)⁻¹) ≤ (2:ℝ) ^ (1:ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        rw [inv_le_one_iff₀]
        right
        exact_mod_cast hd
      rwa [Real.rpow_one] at h1
    have hqle : (q:ℝ) ≤ 3 * m ^ ((d:ℝ)⁻¹) := by
      have hlt : (q:ℝ) < (2 * m) ^ ((d:ℝ)⁻¹) + 1 := Nat.ceil_lt_add_one hbase
      rw [hsplit] at hlt
      nlinarith [hmd, h2d]
    have hqsq : ((q:ℝ)) ^ 2 ≤ 9 * m ^ ((2:ℝ) / (d:ℝ)) := by
      have hid : (m ^ ((d:ℝ)⁻¹)) ^ 2 = m ^ ((2:ℝ) / (d:ℝ)) := by
        rw [← Real.rpow_natCast (m ^ ((d:ℝ)⁻¹)) 2, ← Real.rpow_mul (le_of_lt hmpos)]
        congr 1
        push_cast
        field_simp
      have hqnn : (0:ℝ) ≤ (q:ℝ) := by positivity
      nlinarith [hqle, hmd, hid]
    have hfin := T_le_of_box hd A q hq
    have hcast : ((d * q : ℕ) : ℝ) ^ 2 = (d:ℝ) ^ 2 * (q:ℝ) ^ 2 := by push_cast; ring
    rw [hcast] at hfin
    have hmrw : m ^ ((2:ℝ) / (d:ℝ)) * m = m ^ (1 + (2:ℝ) / (d:ℝ)) := by
      rw [Real.rpow_add hmpos, Real.rpow_one]
      ring
    calc T A ≤ 8 * ((d:ℝ) ^ 2 * (q:ℝ) ^ 2) * m := by rw [← hm] at hfin; exact hfin
      _ ≤ 8 * ((d:ℝ) ^ 2 * (9 * m ^ ((2:ℝ) / (d:ℝ)))) * m := by
          have hmnn : (0:ℝ) ≤ m := le_of_lt hmpos
          gcongr
      _ = 72 * (d:ℝ) ^ 2 * (m ^ ((2:ℝ) / (d:ℝ)) * m) := by ring
      _ = 72 * (d:ℝ) ^ 2 * m ^ (1 + (2:ℝ) / (d:ℝ)) := by rw [hmrw]

end ORRW.Support
