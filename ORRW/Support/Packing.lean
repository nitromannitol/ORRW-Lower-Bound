/-
Supporting lemmas for the increment packing estimate of Bou-Rabee--Peres,
Section 8, `orrw.tex` (label `lem:gradient-packing`).

Nothing here is frozen; the file exists only to supply
`ORRW/Frozen/Return/IncrementPacking.lean` with the two ingredients of the
paper's proof.

* An abstract packing estimate, `abstract_packing`: if an `ℕ`-valued "level"
  function on a finite set `F` has fibres of cardinality at most
  `K (1+r)^{d-1}`, then `∑_{e ∈ F} (1 + level e)^{1-d} ≤ (2K+1)|F|^{1/d}`.
  This is the paper's splitting at `R = ⌈m^{1/d}⌉`: the levels below `R`
  contribute at most `K` each, and the levels above `R` contribute at most
  `m R^{1-d}`.

* The geometric input, `count_fibre`: at most `4d²(2r+1)^{d-1}` edges of `ℤ^d`
  have `min(‖x‖, ‖y‖) = r`.  This is the paper's "at most `C r^{d-1}` edges
  have `min(‖x‖,‖y‖) = r`".  The proof encodes such an edge by its step
  vector, the sign of one extremal coordinate of its inner endpoint, and that
  endpoint with the extremal coordinate deleted.
-/
import Mathlib
import ORRW.Basic
import ORRW.Lattice

open Finset

namespace ORRW.Support

/-! ## The abstract packing estimate -/

private theorem inner_bound {α : Type*} [DecidableEq α] {d : ℕ}
    {K : ℝ} (lvl : α → ℕ) (F : Finset α) (N : ℕ)
    (hcount : ∀ r : ℕ, ((F.filter (fun e => lvl e = r)).card : ℝ)
        ≤ K * (1 + (r : ℝ)) ^ (d - 1)) :
    ∑ e ∈ F.filter (fun e => lvl e < N), (1 : ℝ) / (1 + (lvl e : ℝ)) ^ (d - 1)
      ≤ K * (N : ℝ) := by
  classical
  have hmaps : ∀ e ∈ F.filter (fun e => lvl e < N), lvl e ∈ Finset.range N := by
    intro e he
    exact Finset.mem_range.mpr (Finset.mem_filter.mp he).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
        (fun e => (1 : ℝ) / (1 + (lvl e : ℝ)) ^ (d - 1))]
  have hb : ∀ r ∈ Finset.range N,
      ∑ e ∈ (F.filter (fun e => lvl e < N)).filter (fun e => lvl e = r),
        (1 : ℝ) / (1 + (lvl e : ℝ)) ^ (d - 1) ≤ K := by
    intro r _
    have hstep : ∑ e ∈ (F.filter (fun e => lvl e < N)).filter (fun e => lvl e = r),
        (1 : ℝ) / (1 + (lvl e : ℝ)) ^ (d - 1)
        = (((F.filter (fun e => lvl e < N)).filter (fun e => lvl e = r)).card : ℝ)
            * ((1 : ℝ) / (1 + (r : ℝ)) ^ (d - 1)) := by
      rw [Finset.sum_congr rfl (fun e he => by rw [(Finset.mem_filter.mp he).2]),
        Finset.sum_const, nsmul_eq_mul]
    rw [hstep]
    have hsub : (((F.filter (fun e => lvl e < N)).filter (fun e => lvl e = r)).card : ℝ)
        ≤ K * (1 + (r : ℝ)) ^ (d - 1) := by
      refine le_trans ?_ (hcount r)
      exact_mod_cast Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
    have hpos : (0:ℝ) < (1 + (r : ℝ)) ^ (d - 1) := by positivity
    rw [mul_one_div, div_le_iff₀ hpos]
    exact hsub
  calc ∑ r ∈ Finset.range N,
        ∑ e ∈ (F.filter (fun e => lvl e < N)).filter (fun e => lvl e = r),
          (1 : ℝ) / (1 + (lvl e : ℝ)) ^ (d - 1)
      ≤ ∑ _r ∈ Finset.range N, K := Finset.sum_le_sum hb
    _ = K * (N : ℝ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

private theorem outer_bound {α : Type*} [DecidableEq α] {d : ℕ}
    (lvl : α → ℕ) (F : Finset α) (N : ℕ) (hN : 0 < N) :
    ∑ e ∈ F.filter (fun e => ¬ lvl e < N), (1 : ℝ) / (1 + (lvl e : ℝ)) ^ (d - 1)
      ≤ (F.card : ℝ) / (N : ℝ) ^ (d - 1) := by
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have key : ∀ e ∈ F.filter (fun e => ¬ lvl e < N),
      (1 : ℝ) / (1 + (lvl e : ℝ)) ^ (d - 1) ≤ 1 / (N:ℝ) ^ (d-1) := by
    intro e he
    have he' : N ≤ lvl e := by
      have := (Finset.mem_filter.mp he).2
      omega
    have h1 : (N:ℝ) ≤ 1 + (lvl e : ℝ) := by
      have : (N:ℝ) ≤ (lvl e : ℝ) := by exact_mod_cast he'
      linarith
    have h2 : (N:ℝ) ^ (d-1) ≤ (1 + (lvl e : ℝ)) ^ (d-1) := by gcongr
    exact one_div_le_one_div_of_le (by positivity) h2
  calc ∑ e ∈ F.filter (fun e => ¬ lvl e < N), (1 : ℝ) / (1 + (lvl e : ℝ)) ^ (d - 1)
      ≤ (F.filter (fun e => ¬ lvl e < N)).card • ((1:ℝ) / (N:ℝ) ^ (d-1)) :=
        Finset.sum_le_card_nsmul _ _ _ key
    _ ≤ (F.card : ℝ) / (N:ℝ) ^ (d-1) := by
        rw [nsmul_eq_mul]
        have : ((F.filter (fun e => ¬ lvl e < N)).card : ℝ) ≤ (F.card : ℝ) := by
          exact_mod_cast Finset.card_filter_le _ _
        rw [mul_one_div]
        gcongr

/-- Abstract packing estimate.  If the fibres of an `ℕ`-valued level function
on a finite set `F` have cardinality at most `K (1+r)^{d-1}`, then the
`(1+r)^{1-d}`-weighted sum over `F` is at most `(2K+1)|F|^{1/d}`.

This is the splitting of `lem:gradient-packing` at `R = ⌈m^{1/d}⌉`. -/
theorem abstract_packing {α : Type*} [DecidableEq α] {d : ℕ} (hd : 2 ≤ d)
    {K : ℝ} (hK : 0 ≤ K) (lvl : α → ℕ) (F : Finset α)
    (hcount : ∀ r : ℕ, ((F.filter (fun e => lvl e = r)).card : ℝ)
        ≤ K * (1 + (r : ℝ)) ^ (d - 1)) :
    ∑ e ∈ F, (1 : ℝ) / (1 + (lvl e : ℝ)) ^ (d - 1)
      ≤ (2 * K + 1) * (F.card : ℝ) ^ ((1 : ℝ) / (d : ℝ)) := by
  classical
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hd
  have hinvne : ((d:ℝ))⁻¹ ≠ 0 := by positivity
  rcases Nat.eq_zero_or_pos F.card with hm0 | hm
  · have hF : F = ∅ := Finset.card_eq_zero.mp hm0
    subst hF
    simp [Real.zero_rpow hinvne]
  set m : ℕ := F.card with hmdef
  set N : ℕ := ⌈(m : ℝ) ^ ((1:ℝ)/(d:ℝ))⌉₊ with hNdef
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hpow1 : (1:ℝ) ≤ (m:ℝ) ^ ((1:ℝ)/(d:ℝ)) := Real.one_le_rpow hmR (by positivity)
  have hNge : (m:ℝ) ^ ((1:ℝ)/(d:ℝ)) ≤ (N:ℝ) := Nat.le_ceil _
  have hNle : (N:ℝ) ≤ (m:ℝ) ^ ((1:ℝ)/(d:ℝ)) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le (by norm_num) (le_trans hpow1 hNge)
  have hNnat : 0 < N := by exact_mod_cast hNpos
  rw [← Finset.sum_filter_add_sum_filter_not F (fun e => lvl e < N)]
  have hinner := inner_bound (d := d) (K := K) lvl F N hcount
  have houter := outer_bound (d := d) lvl F N hNnat
  have hA : K * (N:ℝ) ≤ 2 * K * (m:ℝ) ^ ((1:ℝ)/(d:ℝ)) := by nlinarith
  have hB : (m:ℝ) / (N:ℝ) ^ (d-1) ≤ (m:ℝ) ^ ((1:ℝ)/(d:ℝ)) := by
    have hA0 : (0:ℝ) ≤ (m:ℝ) ^ ((1:ℝ)/(d:ℝ)) := Real.rpow_nonneg (by linarith) _
    have hkey : ((m:ℝ) ^ ((1:ℝ)/(d:ℝ))) ^ (d-1) * ((m:ℝ) ^ ((1:ℝ)/(d:ℝ))) = (m:ℝ) := by
      rw [← pow_succ, Nat.sub_add_cancel hd1, ← Real.rpow_natCast ((m:ℝ) ^ ((1:ℝ)/(d:ℝ))) d,
        ← Real.rpow_mul (by linarith)]
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hd0), Real.rpow_one]
    have hNd : (0:ℝ) < (N:ℝ) ^ (d-1) := by positivity
    rw [div_le_iff₀ hNd]
    calc (m:ℝ) = ((m:ℝ) ^ ((1:ℝ)/(d:ℝ))) ^ (d-1) * ((m:ℝ) ^ ((1:ℝ)/(d:ℝ))) := hkey.symm
      _ ≤ (N:ℝ) ^ (d-1) * ((m:ℝ) ^ ((1:ℝ)/(d:ℝ))) := by gcongr
      _ = (m:ℝ) ^ ((1:ℝ)/(d:ℝ)) * (N:ℝ) ^ (d-1) := by ring
  linarith [hinner.trans hA, houter.trans hB]

/-! ## The sup norm as a natural number -/

/-- The sup norm of a lattice point, as a natural number. -/
def nrm {d : ℕ} (x : Site d) : ℕ := Finset.univ.sup fun i => (x i).natAbs

/-- Every coordinate of a site is bounded by its norm, the basic pointwise estimate underlying the fibre counting bound. -/
lemma le_nrm {d : ℕ} (x : Site d) (i : Fin d) : (x i).natAbs ≤ nrm x :=
  Finset.le_sup (f := fun j => (x j).natAbs) (Finset.mem_univ i)

/-- Provides a site whose norm equals the given positive norm, so that fibre levels can be realized by actual sites when applying the abstract packing estimate. -/
lemma exists_eq_nrm {d : ℕ} (hd : 0 < d) (x : Site d) :
    ∃ i : Fin d, (x i).natAbs = nrm x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hd)) (fun j => (x j).natAbs)
  exact ⟨i, hi.symm⟩

/-- Bridges the integer-valued norm used for counting fibres to the real norm on sites, so the packing estimate's level bounds can be applied to edge counts. -/
lemma nrm_cast {d : ℕ} (hd : 0 < d) (x : Site d) : (nrm x : ℝ) = ‖x‖ := by
  obtain ⟨i₀, hi₀⟩ := exists_eq_nrm hd x
  refine le_antisymm ?_ ?_
  · have h : ‖x i₀‖ ≤ ‖x‖ := norm_le_pi_norm x i₀
    rw [← hi₀]
    simpa [Int.norm_eq_abs, Nat.cast_natAbs] using h
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    have h : ((x i).natAbs : ℝ) ≤ (nrm x : ℝ) := by exact_mod_cast le_nrm x i
    simpa [Int.norm_eq_abs, Nat.cast_natAbs] using h

/-! ## The level of an edge, and the fibre count -/

/-- The level of an unordered edge: the smaller of the two sup norms. -/
def lvl {d : ℕ} : Sym2 (Site d) → ℕ :=
  Sym2.lift ⟨fun x y => min (nrm x) (nrm y), fun _ _ => min_comm _ _⟩

@[simp] lemma lvl_mk {d : ℕ} (x y : Site d) : lvl s(x, y) = min (nrm x) (nrm y) := rfl

open Classical in
/-- A choice of ordered representative of an edge, with the endpoint of smaller
sup norm first. -/
noncomputable def rep {d : ℕ} (e : Sym2 (Site d)) : Site d × Site d :=
  if h : ∃ p : Site d × Site d, e = s(p.1, p.2) ∧ Adj p.1 p.2 ∧ nrm p.1 ≤ nrm p.2
  then h.choose else (0, 0)

/-- Provides, for an adjacent edge, a canonical ordered representative whose endpoints are again adjacent, so that counting arguments can pass from unordered edges to chosen endpoints. -/
lemma rep_spec {d : ℕ} {e : Sym2 (Site d)} (h : ∃ x y : Site d, e = s(x, y) ∧ Adj x y) :
    e = s((rep e).1, (rep e).2) ∧ Adj (rep e).1 (rep e).2
      ∧ nrm (rep e).1 ≤ nrm (rep e).2 := by
  classical
  have h' : ∃ p : Site d × Site d, e = s(p.1, p.2) ∧ Adj p.1 p.2 ∧ nrm p.1 ≤ nrm p.2 := by
    obtain ⟨x, y, hxy, hadj⟩ := h
    rcases le_total (nrm x) (nrm y) with hle | hle
    · exact ⟨(x, y), hxy, hadj, hle⟩
    · exact ⟨(y, x), by rw [hxy, Sym2.eq_swap], (adj_comm x y).mp hadj, hle⟩
  rw [rep, dif_pos h']
  exact h'.choose_spec

/-- Provides a canonical representative of an edge as an ordered pair of adjacent sites, so that fibre-counting arguments can speak of the edge's inner endpoint and its coordinates. -/
lemma rep_nrm {d : ℕ} {e : Sym2 (Site d)} (h : ∃ x y : Site d, e = s(x, y) ∧ Adj x y) :
    nrm (rep e).1 = lvl e := by
  obtain ⟨he, _, hle⟩ := rep_spec h
  conv_rhs => rw [he]
  rw [lvl_mk, min_eq_left hle]

/-- The `i`-th coordinate slice of the box of radius `r`, with the `i`-th
coordinate pinned to `0`. -/
def slice {d : ℕ} (r : ℕ) (i : Fin d) : Finset (Site d) :=
  Fintype.piFinset (fun j => if j = i then ({0} : Finset ℤ) else Finset.Icc (-(r:ℤ)) (r:ℤ))

/-- Counts the edges of the range whose inner endpoint has extremal coordinate i equal to r, giving the per-slice bound that sum over i yields the fibre estimate. -/
lemma card_slice {d : ℕ} (r : ℕ) (i : Fin d) :
    (slice r i).card = (2 * r + 1) ^ (d - 1) := by
  rw [slice, Fintype.card_piFinset]
  have hc : ∀ j : Fin d,
      (if j = i then ({0} : Finset ℤ) else Finset.Icc (-(r:ℤ)) (r:ℤ)).card
        = if j = i then 1 else 2 * r + 1 := by
    intro j
    by_cases hj : j = i
    · simp [hj]
    · simp only [hj, if_false]
      rw [Int.card_Icc]
      omega
  rw [Finset.prod_congr rfl (fun j _ => hc j)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  rw [if_pos rfl, one_mul]
  rw [Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

open Classical in
/-- The encoding used in the counting argument: an edge is determined by its
step vector, the sign of the `i`-th coordinate of its inner endpoint, and that
endpoint with the `i`-th coordinate deleted. -/
noncomputable def enc {d : ℕ} (i : Fin d) (e : Sym2 (Site d)) : (Site d × Bool) × Site d :=
  (((rep e).2 - (rep e).1, decide (0 ≤ (rep e).1 i)), Function.update (rep e).1 i 0)

/-- Bounds the number of range-r edges in one coordinate direction, the per-direction factor in the fibre count for the packing estimate. -/
lemma count_one_dir {d : ℕ} (F : Finset (Sym2 (Site d)))
    (hF : ∀ e ∈ F, ∃ x y : Site d, e = s(x, y) ∧ Adj x y) (r : ℕ) (i : Fin d) :
    ((F.filter (fun e => lvl e = r)).filter
        (fun e => ((rep e).1 i).natAbs = r)).card
      ≤ 4 * d * (2 * r + 1) ^ (d - 1) := by
  classical
  set G := (F.filter (fun e => lvl e = r)).filter
      (fun e => ((rep e).1 i).natAbs = r) with hG
  set T : Finset ((Site d × Bool) × Site d) :=
    (((Finset.univ : Finset (Dir d)).image dirVec) ×ˢ (Finset.univ : Finset Bool))
      ×ˢ slice r i with hT
  have hex : ∀ e ∈ G, ∃ x y : Site d, e = s(x, y) ∧ Adj x y := by
    intro e he
    exact hF e (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
  have hnr : ∀ e ∈ G, nrm (rep e).1 = r := by
    intro e he
    rw [rep_nrm (hex e he)]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
  have hmem : ∀ e ∈ G, enc i e ∈ T := by
    intro e he
    obtain ⟨_, hadj, _⟩ := rep_spec (hex e he)
    obtain ⟨a, ha⟩ := hadj
    refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
    · refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      show dirVec a = (rep e).2 - (rep e).1
      rw [ha]; abel
    · refine Fintype.mem_piFinset.mpr ?_
      intro j
      show Function.update (rep e).1 i 0 j ∈ _
      by_cases hj : j = i
      · subst hj
        simp
      · rw [Function.update_of_ne hj]
        simp only [hj, if_false]
        have hb : ((rep e).1 j).natAbs ≤ nrm (rep e).1 := le_nrm _ j
        have hr : nrm (rep e).1 = r := hnr e he
        rw [Finset.mem_Icc]
        omega
  have hinj : Set.InjOn (enc i) G := by
    intro e₁ he₁ e₂ he₂ heq
    simp only [enc, Prod.mk.injEq] at heq
    obtain ⟨⟨hdiff, hsign⟩, hupd⟩ := heq
    have h1 : ((rep e₁).1 i).natAbs = r := (Finset.mem_filter.mp he₁).2
    have h2 : ((rep e₂).1 i).natAbs = r := (Finset.mem_filter.mp he₂).2
    have hs : (0 ≤ (rep e₁).1 i) ↔ (0 ≤ (rep e₂).1 i) := by
      simpa using decide_eq_decide.mp hsign
    have hx : (rep e₁).1 = (rep e₂).1 := by
      funext j
      by_cases hj : j = i
      · subst hj
        omega
      · have := congrFun hupd j
        rwa [Function.update_of_ne hj, Function.update_of_ne hj] at this
    have hy : (rep e₁).2 = (rep e₂).2 := by
      rw [hx] at hdiff
      exact sub_left_inj.mp hdiff
    obtain ⟨hr1, _, _⟩ := rep_spec (hex e₁ he₁)
    obtain ⟨hr2, _, _⟩ := rep_spec (hex e₂ he₂)
    rw [hr1, hr2, hx, hy]
  have hcard := Finset.card_le_card_of_injOn (enc i) hmem hinj
  refine hcard.trans ?_
  rw [hT, Finset.card_product, Finset.card_product, card_slice]
  have h1 : ((Finset.univ : Finset (Dir d)).image dirVec).card ≤ 2 * d := by
    refine le_trans (Finset.card_image_le) ?_
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  have h2 : (Finset.univ : Finset Bool).card = 2 := by simp
  calc ((Finset.univ : Finset (Dir d)).image dirVec).card * (Finset.univ : Finset Bool).card
        * (2 * r + 1) ^ (d - 1)
      ≤ (2 * d) * 2 * (2 * r + 1) ^ (d - 1) := by
        rw [h2]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
    _ = 4 * d * (2 * r + 1) ^ (d - 1) := by ring

/-- At most `4d²(2r+1)^{d-1}` edges of `F` have `min(‖x‖, ‖y‖) = r`.  This is
the paper's "at most `C r^{d-1}` edges have `min(‖x‖,‖y‖) = r`". -/
lemma count_fibre {d : ℕ} (hd : 0 < d) (F : Finset (Sym2 (Site d)))
    (hF : ∀ e ∈ F, ∃ x y : Site d, e = s(x, y) ∧ Adj x y) (r : ℕ) :
    (F.filter (fun e => lvl e = r)).card ≤ 4 * d * d * (2 * r + 1) ^ (d - 1) := by
  classical
  set S := F.filter (fun e => lvl e = r) with hS
  have hsub : S ⊆ Finset.univ.biUnion
      (fun i : Fin d => S.filter (fun e => ((rep e).1 i).natAbs = r)) := by
    intro e he
    have hex : ∃ x y : Site d, e = s(x, y) ∧ Adj x y :=
      hF e (Finset.mem_filter.mp he).1
    obtain ⟨i, hi⟩ := exists_eq_nrm hd (rep e).1
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
    rw [hi, rep_nrm hex]
    exact (Finset.mem_filter.mp he).2
  calc S.card
      ≤ (Finset.univ.biUnion
          (fun i : Fin d => S.filter (fun e => ((rep e).1 i).natAbs = r))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i : Fin d, (S.filter (fun e => ((rep e).1 i).natAbs = r)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin d, 4 * d * (2 * r + 1) ^ (d - 1) :=
        Finset.sum_le_sum (fun i _ => count_one_dir F hF r i)
    _ = 4 * d * d * (2 * r + 1) ^ (d - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        ring

/-! ## The packing estimate -/

/-- The increment packing estimate of `lem:gradient-packing`, in the exact form
frozen in `ORRW/Frozen/Return/IncrementPacking.lean`. -/
theorem increment_packing (d : ℕ) (hd : 2 ≤ d) (C : ℝ) :
    ∃ C' : ℝ, ∀ a : Site d → ℝ,
      (∀ x y : Site d, Adj x y →
        |a x - a y| ≤ C / (1 + min ‖x‖ ‖y‖) ^ (d - 1)) →
      ∀ F : Finset (Sym2 (Site d)),
        (∀ e ∈ F, ∃ x y : Site d, e = s(x, y) ∧ Adj x y) →
        ∑ e ∈ F, Sym2.lift ⟨fun x y => |a x - a y|,
            fun x y => abs_sub_comm (a x) (a y)⟩ e
          ≤ C' * (F.card : ℝ) ^ ((1 : ℝ) / (d : ℝ)) := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  set K : ℝ := 4 * (d:ℝ) * (d:ℝ) * 2 ^ (d - 1) with hK
  have hK0 : (0:ℝ) ≤ K := by positivity
  refine ⟨max C 0 * (2 * K + 1), ?_⟩
  intro a ha F hF
  have hCp : (0:ℝ) ≤ max C 0 := le_max_right _ _
  have hpt : ∀ e ∈ F, Sym2.lift ⟨fun x y => |a x - a y|,
      fun x y => abs_sub_comm (a x) (a y)⟩ e
        ≤ max C 0 * ((1:ℝ) / (1 + (lvl e : ℝ)) ^ (d - 1)) := by
    intro e he
    obtain ⟨x, y, rfl, hadj⟩ := hF e he
    rw [Sym2.lift_mk]
    have hmin : ((lvl s(x, y) : ℕ) : ℝ) = min ‖x‖ ‖y‖ := by
      rw [lvl_mk, Nat.cast_min, nrm_cast hd0, nrm_cast hd0]
    have h1 : |a x - a y| ≤ C / (1 + min ‖x‖ ‖y‖) ^ (d - 1) := ha x y hadj
    have h2 : C / (1 + min ‖x‖ ‖y‖) ^ (d - 1)
        ≤ max C 0 / (1 + min ‖x‖ ‖y‖) ^ (d - 1) := by
      gcongr
      exact le_max_left _ _
    rw [mul_one_div, hmin]
    exact h1.trans h2
  have hsum : ∑ e ∈ F, Sym2.lift ⟨fun x y => |a x - a y|,
      fun x y => abs_sub_comm (a x) (a y)⟩ e
        ≤ ∑ e ∈ F, max C 0 * ((1:ℝ) / (1 + (lvl e : ℝ)) ^ (d - 1)) :=
    Finset.sum_le_sum hpt
  have hcount : ∀ r : ℕ, ((F.filter (fun e => lvl e = r)).card : ℝ)
      ≤ K * (1 + (r : ℝ)) ^ (d - 1) := by
    intro r
    have h := count_fibre hd0 F hF r
    have h2 : (2 * r + 1) ^ (d - 1) ≤ 2 ^ (d - 1) * (r + 1) ^ (d - 1) := by
      rw [← Nat.mul_pow]
      exact Nat.pow_le_pow_left (by omega) _
    have h3 : (F.filter (fun e => lvl e = r)).card
        ≤ 4 * d * d * (2 ^ (d - 1) * (r + 1) ^ (d - 1)) :=
      h.trans (Nat.mul_le_mul_left _ h2)
    have h4 : ((F.filter (fun e => lvl e = r)).card : ℝ)
        ≤ ((4 * d * d * (2 ^ (d - 1) * (r + 1) ^ (d - 1)) : ℕ) : ℝ) := by
      exact_mod_cast h3
    refine h4.trans ?_
    push_cast
    rw [hK]
    ring_nf
    rfl
  have hpack := abstract_packing (α := Sym2 (Site d)) hd hK0 lvl F hcount
  calc ∑ e ∈ F, Sym2.lift ⟨fun x y => |a x - a y|,
        fun x y => abs_sub_comm (a x) (a y)⟩ e
      ≤ ∑ e ∈ F, max C 0 * ((1:ℝ) / (1 + (lvl e : ℝ)) ^ (d - 1)) := hsum
    _ = max C 0 * ∑ e ∈ F, (1:ℝ) / (1 + (lvl e : ℝ)) ^ (d - 1) := by
        rw [Finset.mul_sum]
    _ ≤ max C 0 * ((2 * K + 1) * (F.card : ℝ) ^ ((1 : ℝ) / (d : ℝ))) :=
        mul_le_mul_of_nonneg_left hpack hCp
    _ = max C 0 * (2 * K + 1) * (F.card : ℝ) ^ ((1 : ℝ) / (d : ℝ)) := by ring

end ORRW.Support
