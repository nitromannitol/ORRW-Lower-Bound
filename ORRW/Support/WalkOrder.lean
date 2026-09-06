/-
Supporting lemmas for Lemma 3.2 of Bou-Rabee--Peres (`lem:walk-order`,
`orrw.tex`): an ordering of the sites the walk has visited for which each
`S_{σ_j}` is an initial segment.

The file has four parts.

* Arithmetic of `σ`: `|E_{σ_j}| = j` exactly, `σ` is strictly increasing, and the
  step taken at time `σ_j` crosses an edge that was untraversed before.

* `|R_m| ≤ |E_m| + 1`, the model's form of `orrw.tex` ("The edges of
  `E_{σ_k}` form a connected subgraph with `k` edges whose vertex set is `V`").
  The injection sends a site other than the origin to the edge by which the walk
  first reached it.

* The sorting key.  The paper orders `V` by `ι(x)`, the largest `j ≤ k` for which
  `x` is an endpoint of the `j`th distinct edge, breaking ties by placing `v_j`
  before `w_j`.  Since `|E_m|` is nondecreasing, ordering by `ι` is the same as
  ordering by the *time* of that edge, and the time is what is used here:
  `lastNew w K x` is the last `t ≤ K` at which a previously untraversed edge
  incident to `x` was crossed.  The tie-break is the last bit of
  `key = 2 * lastNew + (0 if x is the departure site, 1 if the arrival site)`.

* A generic enumeration lemma: a key injective on a finite set enumerates it.
-/
import ORRW.Potential
import ORRW.Support.Drift

namespace ORRW.Support

open Finset ORRW

variable {d n : ℕ}


/-- The number of distinct edges traversed by the walk increases by exactly one at each step before the horizon. -/
lemma E_succ_eq (w : Fin n → Dir d) {t : ℕ} (ht : t < n) :
    E w (t + 1) = insert (edgeAt w t) (E w t) := by
  unfold E
  rw [Nat.min_eq_left (by omega : t + 1 ≤ n), Nat.min_eq_left (by omega : t ≤ n),
    Finset.range_add_one, Finset.image_insert]

/-- Once the walk has exhausted all its steps the range of traversed edges stops growing, so the edge count at any later time equals the final one. -/
lemma E_succ_eq_of_ge (w : Fin n → Dir d) {t : ℕ} (ht : n ≤ t) :
    E w (t + 1) = E w t := by
  unfold E
  rw [Nat.min_eq_right (by omega : n ≤ t + 1), Nat.min_eq_right ht]

/-- The number of distinct edges traversed by the walk grows by at most one per step, underpinning the bound on the range size used in the ordering argument. -/
lemma card_E_succ_le (w : Fin n → Dir d) (t : ℕ) :
    (E w (t + 1)).card ≤ (E w t).card + 1 := by
  by_cases ht : t < n
  · rw [E_succ_eq w ht]
    exact Finset.card_insert_le _ _
  · rw [E_succ_eq_of_ge w (by omega)]
    omega

/-- Bounds the stopping index of the ordering by the number of distinct edges traversed, ensuring each site in the walk's range is enumerated before the horizon. -/
lemma sigma_le_horizon (w : Fin n → Dir d) {j : ℕ} (hfin : j ≤ (E w n).card) :
    sigma w j ≤ n := (sigma_le_iff w (le_refl n)).mpr hfin

/-- Bounds the number of distinct edges traversed by the walk up to time n in terms of the ordering index j, so that the initial-segment property of the visited sites can be applied at each stage of the enumeration. -/
lemma le_card_E_sigma (w : Fin n → Dir d) {j : ℕ} (hfin : j ≤ (E w n).card) :
    j ≤ (E w (sigma w j)).card :=
  (sigma_le_iff w (sigma_le_horizon w hfin)).mp (le_refl _)

/-- The visit-ordering times are positive once the walk has made at least one step, so the initial-segment argument starts from a genuine site. -/
lemma sigma_pos (w : Fin n → Dir d) {j : ℕ} (hj : 1 ≤ j) : 1 ≤ sigma w j := by
  by_contra hc
  push_neg at hc
  have h0 : sigma w j ≤ 0 := by omega
  have := (sigma_le_iff w (Nat.zero_le n)).mp h0
  rw [ORRW.E_zero] at this
  simp only [Finset.card_empty] at this
  omega

/-- Minimality of `σ_j`: strictly before it, fewer than `j` edges have been crossed. -/
lemma card_E_lt_of_lt_sigma (w : Fin n → Dir d) {j t : ℕ} (ht : t < sigma w j) (htn : t ≤ n) :
    (E w t).card < j := by
  by_contra hc
  push_neg at hc
  have := (sigma_le_iff w htn).mpr hc
  omega

/-- `|E_{σ_j}| = j` exactly. -/
lemma card_E_sigma (w : Fin n → Dir d) {j : ℕ} (hfin : j ≤ (E w n).card) :
    (E w (sigma w j)).card = j := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    rw [ORRW.sigma_zero, ORRW.E_zero]
    simp
  · have hge := le_card_E_sigma w hfin
    have hs1 : 1 ≤ sigma w j := sigma_pos w hj
    have hle : sigma w j ≤ n := sigma_le_horizon w hfin
    obtain ⟨t, ht⟩ : ∃ t, sigma w j = t + 1 := ⟨sigma w j - 1, by omega⟩
    have hlt : (E w t).card < j :=
      card_E_lt_of_lt_sigma w (by omega) (by omega)
    have hstep := card_E_succ_le w t
    rw [← ht] at hstep
    omega

/-- `σ` is strictly increasing on the indices the horizon supports. -/
lemma sigma_strict_mono (w : Fin n → Dir d) {j₁ j₂ : ℕ} (h : j₁ < j₂)
    (hfin : j₂ ≤ (E w n).card) : sigma w j₁ < sigma w j₂ := by
  by_contra hc
  push_neg at hc
  have h1 : j₁ ≤ (E w n).card := le_trans (le_of_lt h) hfin
  have := (sigma_le_iff w (sigma_le_horizon w h1)).mp hc
  rw [card_E_sigma w h1] at this
  omega

/-- The visit-ordering times σ form a nondecreasing (indeed strictly increasing) sequence in j, so each initial segment S_{σ_j} is nested as required for the ordering in Lemma 3.2. -/
lemma sigma_mono (w : Fin n → Dir d) {j₁ j₂ : ℕ} (h : j₁ ≤ j₂)
    (hfin : j₂ ≤ (E w n).card) : sigma w j₁ ≤ sigma w j₂ := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_refl _
  · exact le_of_lt (sigma_strict_mono w hlt hfin)

/-- The step taken at time `σ_j` crosses an edge that was not traversed before. -/
lemma edge_new_at_sigma (w : Fin n → Dir d) {j : ℕ} (hj : 1 ≤ j) (hfin : j ≤ (E w n).card) :
    edgeAt w (sigma w j - 1) ∉ E w (sigma w j - 1) := by
  have hs1 : 1 ≤ sigma w j := sigma_pos w hj
  have hle : sigma w j ≤ n := sigma_le_horizon w hfin
  obtain ⟨t, ht⟩ : ∃ t, sigma w j = t + 1 := ⟨sigma w j - 1, by omega⟩
  have htn : t < n := by omega
  have hlt : (E w t).card < j := card_E_lt_of_lt_sigma w (by omega) (by omega)
  have hcard : (E w (sigma w j)).card = j := card_E_sigma w hfin
  intro hc
  rw [ht] at hcard
  rw [ht] at hc
  simp only [Nat.add_sub_cancel] at hc
  rw [E_succ_eq w htn, Finset.insert_eq_self.mpr hc] at hcard
  omega

/-- The first time the walk is at `y`. -/
noncomputable def hit (w : Fin n → Dir d) (y : Site d) : ℕ := sInf {i | pos w i = y}

/-- Bounds the exit time of the walk from the origin's neighborhood by the index at which it first reaches the site y. -/
lemma hit_le (w : Fin n → Dir d) {y : Site d} {i : ℕ} (h : pos w i = y) :
    hit w y ≤ i := Nat.sInf_le h

/-- The range of a walk up to time m has positive cardinality whenever the site y has been reached by then. -/
lemma pos_hit (w : Fin n → Dir d) {y : Site d} {m : ℕ} (hy : y ∈ R w m) :
    pos w (hit w y) = y := by
  rw [R, Finset.mem_image] at hy
  obtain ⟨i, _, hi⟩ := hy
  exact Nat.sInf_mem (⟨i, hi⟩ : Set.Nonempty {i | pos w i = y})

/-- Bounds the exit time of a site in the range by the current time, used to relate visits to the ordering of first-traversed edges. -/
lemma hit_le_of_mem (w : Fin n → Dir d) {y : Site d} {m : ℕ} (hy : y ∈ R w m) :
    hit w y ≤ m := by
  rw [R, Finset.mem_image] at hy
  obtain ⟨i, hi, rfl⟩ := hy
  rw [Finset.mem_range] at hi
  exact le_trans (hit_le w rfl) (by omega)

/-- The edge crossed at step `i` belongs to the range of the walk up to time `m`, so newly traversed edges accumulate in `E_m`. -/
lemma edgeAt_mem_E (w : Fin n → Dir d) {i m : ℕ} (him : i < m) (hin : i < n) :
    edgeAt w i ∈ E w m := by
  unfold E
  exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))

/-- The range at time `m` has at most one more element than the traversed-edge set:
the walk's trace is a connected subgraph. -/
lemma card_R_le_card_E (w : Fin n → Dir d) {m : ℕ} (hm : m ≤ n) :
    (R w m).card ≤ (E w m).card + 1 := by
  classical
  have hmem : pos w 0 ∈ R w m := ORRW.pos_mem_R w (Nat.zero_le m)
  have hcard : ((R w m).erase (pos w 0)).card + 1 = (R w m).card :=
    Finset.card_erase_add_one hmem
  have hkey : ∀ y ∈ (R w m).erase (pos w 0), 1 ≤ hit w y ∧ hit w y ≤ m ∧ pos w (hit w y) = y := by
    intro y hy
    have hne : y ≠ pos w 0 := (Finset.mem_erase.mp hy).1
    have hyR : y ∈ R w m := (Finset.mem_erase.mp hy).2
    refine ⟨?_, hit_le_of_mem w hyR, pos_hit w hyR⟩
    by_contra hc
    push_neg at hc
    have h0 : hit w y = 0 := by omega
    exact hne (by rw [← pos_hit w hyR, h0])
  have hinj : ((R w m).erase (pos w 0)).card ≤ (E w m).card := by
    refine Finset.card_le_card_of_injOn (fun y => edgeAt w (hit w y - 1)) ?_ ?_
    · intro y hy
      obtain ⟨h1, h2, _⟩ := hkey y hy
      exact edgeAt_mem_E w (by omega) (by omega)
    · intro y hy z hz hyz
      obtain ⟨hy1, hy2, hy3⟩ := hkey y hy
      obtain ⟨hz1, hz2, hz3⟩ := hkey z hz
      simp only [edgeAt] at hyz
      rw [show hit w y - 1 + 1 = hit w y by omega, show hit w z - 1 + 1 = hit w z by omega,
        hy3, hz3] at hyz
      rcases Sym2.eq_iff.mp hyz with ⟨_, h⟩ | ⟨h1, h2⟩
      · exact h
      · exfalso
        have e1 : hit w z ≤ hit w y - 1 := hit_le w h1
        have e2 : hit w y ≤ hit w z - 1 := hit_le w h2.symm
        omega
  omega

/-- Bounds the number of distinct sites visited by time k by one more than the number of edges traversed, via the injection sending each non-origin site to the edge by which the walk first reached it. -/
lemma card_R_sigma_le (w : Fin n → Dir d) {k : ℕ} (hfin : k ≤ (E w n).card) :
    (R w (sigma w k)).card ≤ k + 1 := by
  have h1 := card_R_le_card_E w (sigma_le_horizon w hfin)
  rwa [card_E_sigma w hfin] at h1


/-! ### The sorting key -/

open Classical in
/-- The times up to `K` at which the walk crosses a previously untraversed edge
incident to `x`. -/
noncomputable def newTimes (w : Fin n → Dir d) (K : ℕ) (x : Site d) : Finset ℕ :=
  (Finset.Icc 1 K).filter (fun t => edgeAt w (t - 1) ∉ E w (t - 1) ∧ x ∈ edgeAt w (t - 1))

/-- Characterizes membership in the list of times at which the walk crosses a previously untraversed edge incident to a given site. -/
lemma mem_newTimes (w : Fin n → Dir d) (K : ℕ) (x : Site d) (t : ℕ) :
    t ∈ newTimes w K x ↔
      (1 ≤ t ∧ t ≤ K) ∧ (edgeAt w (t - 1) ∉ E w (t - 1) ∧ x ∈ edgeAt w (t - 1)) := by
  classical
  unfold newTimes
  rw [Finset.mem_filter, Finset.mem_Icc]

/-- The last time up to `K` at which a previously untraversed edge incident to `x` was
crossed.  This is `orrw.tex`'s `ι(x)`, recorded as a time rather than as an
edge index; the two orderings agree because `|E_m|` is nondecreasing. -/
noncomputable def lastNew (w : Fin n → Dir d) (K : ℕ) (x : Site d) : ℕ :=
  (newTimes w K x).sup id

/-- The last time a previously untraversed edge incident to a site was crossed is bounded by the horizon, anchoring the sorting key used to order the visited sites. -/
lemma le_lastNew {w : Fin n → Dir d} {K : ℕ} {x : Site d} {t : ℕ}
    (h : t ∈ newTimes w K x) : t ≤ lastNew w K x :=
  Finset.le_sup (f := id) h

/-- The last time a previously untraversed edge incident to a site was crossed is bounded by the horizon, so the sorting key is defined at every site in the range. -/
lemma lastNew_mem (w : Fin n → Dir d) (K : ℕ) (x : Site d)
    (h : (newTimes w K x).Nonempty) : lastNew w K x ∈ newTimes w K x := by
  have hmax : lastNew w K x = (newTimes w K x).max' h := by
    rw [Finset.max'_eq_sup', Finset.sup'_eq_sup]
    rfl
  rw [hmax]
  exact Finset.max'_mem _ h

/-- The last time at which a fresh edge incident to the site was crossed is positive. -/
lemma lastNew_pos (w : Fin n → Dir d) (K : ℕ) (x : Site d)
    (h : (newTimes w K x).Nonempty) : 1 ≤ lastNew w K x :=
  (((mem_newTimes w K x _).mp (lastNew_mem w K x h)).1).1

/-- The last time at which a previously untraversed edge incident to a site is crossed is bounded by the horizon. -/
lemma lastNew_le (w : Fin n → Dir d) (K : ℕ) (x : Site d)
    (h : (newTimes w K x).Nonempty) : lastNew w K x ≤ K :=
  (((mem_newTimes w K x _).mp (lastNew_mem w K x h)).1).2

/-- The walk is at site x at the last time a new edge incident to x was crossed, so the recorded time corresponds to an actual visit. -/
lemma lastNew_endpoint (w : Fin n → Dir d) (K : ℕ) (x : Site d)
    (h : (newTimes w K x).Nonempty) :
    x = pos w (lastNew w K x - 1) ∨ x = pos w (lastNew w K x) := by
  have hm := (mem_newTimes w K x _).mp (lastNew_mem w K x h)
  have h1 : 1 ≤ lastNew w K x := hm.1.1
  have hmem := hm.2.2
  unfold edgeAt at hmem
  rw [show lastNew w K x - 1 + 1 = lastNew w K x by omega] at hmem
  exact Sym2.mem_iff.mp hmem

/-- A step really moves. -/
lemma pos_pred_ne (w : Fin n → Dir d) {t : ℕ} (h1 : 1 ≤ t) (h2 : t ≤ n) :
    pos w (t - 1) ≠ pos w t := by
  have htn : t - 1 < n := by omega
  have hstep := ORRW.pos_succ w (t - 1) htn
  rw [show t - 1 + 1 = t by omega] at hstep
  intro hc
  rw [← hc] at hstep
  have hz : dirVec (w ⟨t - 1, htn⟩) = 0 := by
    funext i
    have h := congrFun hstep i
    simp only [Pi.add_apply] at h
    show dirVec (w ⟨t - 1, htn⟩) i = 0
    omega
  exact ORRW.dirVec_ne_zero _ hz

/-- The sorting key: `2 ι(x)`, with the tie-break of `orrw.tex` ("placing
`v_j` before `w_j` whenever both carry the value `j`") in the last bit. -/
noncomputable def key (w : Fin n → Dir d) (K : ℕ) (x : Site d) : ℕ :=
  2 * lastNew w K x + (if x = pos w (lastNew w K x - 1) then 0 else 1)

/-- The sorting key is injective on sites the walk has visited by time K, so the sites can be totally ordered by the time they last gained a new incident edge, with the departure/arrival bit breaking ties. -/
lemma key_inj (w : Fin n → Dir d) (K : ℕ) {x y : Site d}
    (hx : (newTimes w K x).Nonempty) (hy : (newTimes w K y).Nonempty)
    (h : key w K x = key w K y) : x = y := by
  unfold key at h
  by_cases hbx : x = pos w (lastNew w K x - 1) <;> by_cases hby : y = pos w (lastNew w K y - 1)
  · rw [if_pos hbx, if_pos hby] at h
    have ht : lastNew w K x = lastNew w K y := by omega
    rw [hbx, hby, ht]
  · rw [if_pos hbx, if_neg hby] at h
    omega
  · rw [if_neg hbx, if_pos hby] at h
    omega
  · rw [if_neg hbx, if_neg hby] at h
    have ht : lastNew w K x = lastNew w K y := by omega
    have hx2 : x = pos w (lastNew w K x) := (lastNew_endpoint w K x hx).resolve_left hbx
    have hy2 : y = pos w (lastNew w K y) := (lastNew_endpoint w K y hy).resolve_left hby
    rw [hx2, hy2, ht]

/-- The sorting key of a site is bounded by twice the horizon, the bound needed to run the enumeration argument over keys. -/
lemma key_le (w : Fin n → Dir d) (K : ℕ) (x : Site d) :
    key w K x ≤ 2 * lastNew w K x + 1 := by
  unfold key
  split <;> omega

/-- The sorting key of a site visited by the walk is bounded above by the number of distinct edges traversed up to the exit time, a bound needed to enumerate the sites in the ordering used for Lemma 3.2. -/
lemma le_key (w : Fin n → Dir d) (K : ℕ) (x : Site d) :
    2 * lastNew w K x ≤ key w K x := by
  unfold key
  split <;> omega


/-! ### Enumerating a finite set by an injective key -/

/-- An injective key on a finite set gives an enumeration of the set in increasing key
order. -/
lemma exists_ordering {α : Type*} [DecidableEq α] (V : Finset α) (κ : α → ℕ)
    (hinj : ∀ y ∈ V, ∀ z ∈ V, κ y = κ z → y = z) :
    ∃ f : Fin V.card → α, (∀ i, f i ∈ V) ∧ Function.Injective f ∧
      Finset.image f Finset.univ = V ∧
      (∀ i j : Fin V.card, κ (f i) < κ (f j) → i < j) := by
  classical
  have hinj' : Set.InjOn κ (V : Set α) := fun y hy z hz h => hinj y hy z hz h
  have hcard : (V.image κ).card = V.card := Finset.card_image_of_injOn hinj'
  obtain ⟨e⟩ : Nonempty (Fin V.card ≃o {x // x ∈ V.image κ}) :=
    ⟨(V.image κ).orderIsoOfFin hcard⟩
  have hex : ∀ i : Fin V.card, ∃ z, z ∈ V ∧ κ z = ((e i : ℕ)) :=
    fun i => Finset.mem_image.mp (e i).2
  refine ⟨fun i => (hex i).choose, fun i => ((hex i).choose_spec).1, ?_, ?_, ?_⟩
  · intro i j hij
    have h1 : κ ((hex i).choose) = ((e i : ℕ)) := ((hex i).choose_spec).2
    have h2 : κ ((hex j).choose) = ((e j : ℕ)) := ((hex j).choose_spec).2
    have h3 : ((e i : ℕ)) = ((e j : ℕ)) := by rw [← h1, ← h2]; exact congrArg κ hij
    exact e.injective (Subtype.ext h3)
  · have hfinj : Function.Injective (fun i : Fin V.card => (hex i).choose) := by
      intro i j hij
      have h1 : κ ((hex i).choose) = ((e i : ℕ)) := ((hex i).choose_spec).2
      have h2 : κ ((hex j).choose) = ((e j : ℕ)) := ((hex j).choose_spec).2
      have h3 : ((e i : ℕ)) = ((e j : ℕ)) := by rw [← h1, ← h2]; exact congrArg κ hij
      exact e.injective (Subtype.ext h3)
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨i, _, hi⟩ := hy
      rw [← hi]
      exact ((hex i).choose_spec).1
    · rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
  · intro i j hlt
    have h1 : κ ((hex i).choose) = ((e i : ℕ)) := ((hex i).choose_spec).2
    have h2 : κ ((hex j).choose) = ((e j : ℕ)) := ((hex j).choose_spec).2
    simp only at hlt
    rw [h1, h2] at hlt
    have h3 : e i < e j := hlt
    exact e.lt_iff_lt.mp h3

/-! ### The key against `S` and `σ` -/

/-- Every site the walk has visited by time `σ_k` is an endpoint of some edge the walk
crossed for the first time at a step `≤ σ_k`, `orrw.tex`. -/
lemma newTimes_nonempty (w : Fin n → Dir d) {k : ℕ} (hk : 1 ≤ k) (hfin : k ≤ (E w n).card)
    {x : Site d} (hx : x ∈ R w (sigma w k)) : (newTimes w (sigma w k) x).Nonempty := by
  have hKn : sigma w k ≤ n := sigma_le_horizon w hfin
  have hK1 : 1 ≤ sigma w k := sigma_pos w hk
  have hpx : pos w (hit w x) = x := pos_hit w hx
  have hhK : hit w x ≤ sigma w k := hit_le_of_mem w hx
  rcases Nat.eq_zero_or_pos (hit w x) with h0 | h1
  · refine ⟨1, ?_⟩
    rw [mem_newTimes]
    refine ⟨⟨le_refl 1, hK1⟩, ?_, ?_⟩
    · simp only [Nat.sub_self]
      rw [ORRW.E_zero]
      exact Finset.notMem_empty _
    · simp only [Nat.sub_self]
      unfold edgeAt
      rw [← hpx, h0]
      exact Sym2.mem_mk_left _ _
  · refine ⟨hit w x, ?_⟩
    rw [mem_newTimes]
    refine ⟨⟨h1, hhK⟩, ?_, ?_⟩
    · intro hc
      unfold E at hc
      rw [Finset.mem_image] at hc
      obtain ⟨i', hi', hi'e⟩ := hc
      rw [Finset.mem_range] at hi'
      have hi'lt : i' < hit w x - 1 := lt_of_lt_of_le hi' (min_le_left _ _)
      unfold edgeAt at hi'e
      rw [show hit w x - 1 + 1 = hit w x by omega, hpx] at hi'e
      rcases Sym2.eq_iff.mp hi'e with ⟨_, hb⟩ | ⟨ha, _⟩
      · have := hit_le w hb
        omega
      · have := hit_le w ha
        omega
    · unfold edgeAt
      rw [show hit w x - 1 + 1 = hit w x by omega, hpx]
      exact Sym2.mem_mk_right _ _

/-- `orrw.tex`: every edge at a site of `S_m` has been crossed by step `m`, so no
new edge incident to it is crossed after step `m`. -/
lemma lastNew_le_of_mem_S (hd : 0 < d) (w : Fin n → Dir d) {K m : ℕ} (hKn : K ≤ n)
    {y : Site d} (hy : y ∈ S w m) (hne : (newTimes w K y).Nonempty) :
    lastNew w K y ≤ m := by
  by_contra hc
  push_neg at hc
  have hm := (mem_newTimes w K y (lastNew w K y)).mp (lastNew_mem w K y hne)
  have ht1 : 1 ≤ lastNew w K y := hm.1.1
  have htK : lastNew w K y ≤ K := hm.1.2
  have hnotin : edgeAt w (lastNew w K y - 1) ∉ E w (lastNew w K y - 1) := hm.2.1
  have hyin : y ∈ edgeAt w (lastNew w K y - 1) := hm.2.2
  have htn : lastNew w K y - 1 < n := by omega
  have hstep := ORRW.pos_succ w (lastNew w K y - 1) htn
  rw [show lastNew w K y - 1 + 1 = lastNew w K y by omega] at hstep
  have hedge : edgeAt w (lastNew w K y - 1) ∈ E w m := by
    have hyy : y = pos w (lastNew w K y - 1) ∨ y = pos w (lastNew w K y) := by
      unfold edgeAt at hyin
      rw [show lastNew w K y - 1 + 1 = lastNew w K y by omega] at hyin
      exact Sym2.mem_iff.mp hyin
    rcases hyy with h | h
    · have heq : edgeAt w (lastNew w K y - 1)
          = s(y, y + dirVec (w ⟨lastNew w K y - 1, htn⟩)) := by
        unfold edgeAt
        rw [show lastNew w K y - 1 + 1 = lastNew w K y by omega, hstep, ← h]
      rw [heq]
      exact (mem_S_iff hd w m y).mp hy _
    · have hback : pos w (lastNew w K y - 1)
          = y + dirVec (((w ⟨lastNew w K y - 1, htn⟩).1, !(w ⟨lastNew w K y - 1, htn⟩).2)) := by
        have h2 : y = pos w (lastNew w K y - 1) + dirVec (w ⟨lastNew w K y - 1, htn⟩) :=
          h.trans hstep
        rw [ORRW.Support.dirVec_neg, ← sub_eq_add_neg]
        exact eq_sub_of_add_eq h2.symm
      have heq : edgeAt w (lastNew w K y - 1)
          = s(y, y + dirVec (((w ⟨lastNew w K y - 1, htn⟩).1,
                !(w ⟨lastNew w K y - 1, htn⟩).2))) := by
        unfold edgeAt
        rw [show lastNew w K y - 1 + 1 = lastNew w K y by omega, ← h,
          show s(pos w (lastNew w K y - 1), y) = s(y, pos w (lastNew w K y - 1)) from
            Sym2.eq_swap, hback]
      rw [heq]
      exact (mem_S_iff hd w m y).mp hy _
  exact hnotin (E_mono w (by omega) hedge)

/-- The j-th new-edge time σ_j lies among the times at which the walk crosses an untraversed edge, anchoring the ordering used in Lemma 3.2. -/
lemma sigma_mem_newTimes_v (w : Fin n → Dir d) {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (hfin : k ≤ (E w n).card) :
    sigma w j ∈ newTimes w (sigma w k) (pos w (sigma w j - 1)) := by
  have hjfin : j ≤ (E w n).card := le_trans hjk hfin
  rw [mem_newTimes]
  refine ⟨⟨sigma_pos w hj, sigma_mono w hjk hfin⟩, edge_new_at_sigma w hj hjfin, ?_⟩
  unfold edgeAt
  exact Sym2.mem_mk_left _ _

/-- The j-th first-visit time of the walk lies among the times at which a new edge is traversed, up to the range determined by the number of distinct edges crossed. -/
lemma sigma_mem_newTimes_w (w : Fin n → Dir d) {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (hfin : k ≤ (E w n).card) :
    sigma w j ∈ newTimes w (sigma w k) (pos w (sigma w j)) := by
  have hjfin : j ≤ (E w n).card := le_trans hjk hfin
  rw [mem_newTimes]
  refine ⟨⟨sigma_pos w hj, sigma_mono w hjk hfin⟩, edge_new_at_sigma w hj hjfin, ?_⟩
  unfold edgeAt
  rw [show sigma w j - 1 + 1 = sigma w j from by have := sigma_pos w hj; omega]
  exact Sym2.mem_mk_right _ _

/-- `orrw.tex`: if the arrival site of the `j`th new edge is saturated at time
`σ_j`, then `ι(w_j) = j` exactly. -/
lemma lastNew_arrival (hd : 0 < d) (w : Fin n → Dir d) {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (hfin : k ≤ (E w n).card) (hmem : pos w (sigma w j) ∈ S w (sigma w j)) :
    lastNew w (sigma w k) (pos w (sigma w j)) = sigma w j := by
  have hin := sigma_mem_newTimes_w w hj hjk hfin
  have h1 := le_lastNew hin
  have h2 := lastNew_le_of_mem_S hd w (sigma_le_horizon w hfin) hmem ⟨_, hin⟩
  omega

/-- The site reached at the j-th new-edge step carries the arrival bit in its sorting key, pinning down the tie-break used to order the visited sites. -/
lemma key_arrival (hd : 0 < d) (w : Fin n → Dir d) {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (hfin : k ≤ (E w n).card) (hmem : pos w (sigma w j) ∈ S w (sigma w j)) :
    key w (sigma w k) (pos w (sigma w j)) = 2 * sigma w j + 1 := by
  unfold key
  rw [lastNew_arrival hd w hj hjk hfin hmem, if_neg]
  intro hc
  exact pos_pred_ne w (sigma_pos w hj)
    (le_trans (sigma_mono w hjk hfin) (sigma_le_horizon w hfin)) hc.symm

/-- The sorting key of a site entered by the walk is at least that of the site it departed from, as needed for the initial-segment ordering in Lemma 3.2. -/
lemma key_departure_ge (w : Fin n → Dir d) {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    (hfin : k ≤ (E w n).card) :
    2 * sigma w j ≤ key w (sigma w k) (pos w (sigma w j - 1)) := by
  have h1 := le_lastNew (sigma_mem_newTimes_v w hj hjk hfin)
  have h2 := le_key w (sigma w k) (pos w (sigma w j - 1))
  omega

/-- The range of visited sites grows monotonically with the number of steps taken. -/
lemma R_mono (w : Fin n → Dir d) {j k : ℕ} (h : j ≤ k) : R w j ⊆ R w k := by
  unfold R
  refine Finset.image_subset_image ?_
  exact Finset.range_subset_range.mpr (by omega)

/-- Every site visited by the walk up to time m lies in its range, the containment underlying the bound on the number of sites reachable by the exit time. -/
lemma S_subset_R (w : Fin n → Dir d) (m : ℕ) : S w m ⊆ R w m := Finset.filter_subset _ _


/-! ### `lem:walk-order` -/

/-- Lemma 3.2 of the paper (`lem:walk-order`, `orrw.tex`). -/
theorem insertion_order_of (hd : 1 ≤ d) (w : Fin n → Dir d)
    (k : ℕ) (hk : 1 ≤ k) (hfin : k ≤ (E w n).card) :
    (R w (sigma w k)).card ≤ k + 1 ∧
      ∃ x : Fin (R w (sigma w k)).card → Site d,
        Function.Injective x ∧
        Finset.image x Finset.univ = R w (sigma w k) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ i : Fin (R w (sigma w k)).card,
            pos w (sigma w j - 1) = x i →
            S w (sigma w (j - 1)) ⊆ (Finset.Iio i).image x) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ i : Fin (R w (sigma w k)).card,
            pos w (sigma w j) ∈ S w (sigma w j) → pos w (sigma w j) = x i →
            S w (sigma w j) ⊆ insert (x i) ((Finset.Iio i).image x)) ∧
        (∀ j₁ j₂ : ℕ, 1 ≤ j₁ → j₁ ≤ k → 1 ≤ j₂ → j₂ ≤ k →
            pos w (sigma w j₁) ∈ S w (sigma w j₁) →
            pos w (sigma w j₂) ∈ S w (sigma w j₂) →
            pos w (sigma w j₁) = pos w (sigma w j₂) → j₁ = j₂) := by
  classical
  have hd0 : 0 < d := hd
  have hKn : sigma w k ≤ n := sigma_le_horizon w hfin
  refine ⟨card_R_sigma_le w hfin, ?_⟩
  have hkinj : ∀ y ∈ R w (sigma w k), ∀ z ∈ R w (sigma w k),
      key w (sigma w k) y = key w (sigma w k) z → y = z := by
    intro y hy z hz hyz
    exact key_inj w (sigma w k) (newTimes_nonempty w hk hfin hy)
      (newTimes_nonempty w hk hfin hz) hyz
  obtain ⟨f, hfV, hfinj, hfimg, hford⟩ :=
    exists_ordering (R w (sigma w k)) (key w (sigma w k)) hkinj
  have hsurj : ∀ y ∈ R w (sigma w k), ∃ i, f i = y := by
    intro y hy
    have hy' : y ∈ Finset.image f Finset.univ := by rw [hfimg]; exact hy
    rw [Finset.mem_image] at hy'
    obtain ⟨i, _, h⟩ := hy'
    exact ⟨i, h⟩
  refine ⟨f, hfinj, hfimg, ?_, ?_, ?_⟩
  · -- (i)
    intro j hj1 hjk i hvi y hy
    have hjfin : j ≤ (E w n).card := le_trans hjk hfin
    have hj1k : j - 1 ≤ k := by omega
    have hsm : sigma w (j - 1) ≤ sigma w k := sigma_mono w hj1k hfin
    have hyV : y ∈ R w (sigma w k) := R_mono w hsm (S_subset_R w _ hy)
    obtain ⟨i', hi'⟩ := hsurj y hyV
    have hne : (newTimes w (sigma w k) y).Nonempty := newTimes_nonempty w hk hfin hyV
    have hln : lastNew w (sigma w k) y ≤ sigma w (j - 1) :=
      lastNew_le_of_mem_S hd0 w hKn hy hne
    have hkey1 : key w (sigma w k) y ≤ 2 * sigma w (j - 1) + 1 :=
      le_trans (key_le w (sigma w k) y) (by omega)
    have hlt : sigma w (j - 1) < sigma w j := sigma_strict_mono w (by omega) hjfin
    have hkey2 : 2 * sigma w j ≤ key w (sigma w k) (pos w (sigma w j - 1)) :=
      key_departure_ge w hj1 hjk hfin
    have hlt2 : key w (sigma w k) (f i') < key w (sigma w k) (f i) := by
      rw [hi', ← hvi]
      omega
    exact Finset.mem_image.mpr ⟨i', Finset.mem_Iio.mpr (hford i' i hlt2), hi'⟩
  · -- (ii)
    intro j hj1 hjk i hmem hwi z hz
    have hsm : sigma w j ≤ sigma w k := sigma_mono w hjk hfin
    have hzV : z ∈ R w (sigma w k) := R_mono w hsm (S_subset_R w _ hz)
    obtain ⟨i', hi'⟩ := hsurj z hzV
    have hne : (newTimes w (sigma w k) z).Nonempty := newTimes_nonempty w hk hfin hzV
    have hln : lastNew w (sigma w k) z ≤ sigma w j :=
      lastNew_le_of_mem_S hd0 w hKn hz hne
    have hkey1 : key w (sigma w k) z ≤ 2 * sigma w j + 1 :=
      le_trans (key_le w (sigma w k) z) (by omega)
    have hkey2 : key w (sigma w k) (pos w (sigma w j)) = 2 * sigma w j + 1 :=
      key_arrival hd0 w hj1 hjk hfin hmem
    have hle : key w (sigma w k) (f i') ≤ key w (sigma w k) (f i) := by
      rw [hi', ← hwi, hkey2]
      omega
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hff : f i' = f i := hkinj _ (hfV i') _ (hfV i) heq
      exact Finset.mem_insert.mpr (Or.inl (by rw [← hi', hff]))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_image.mpr ⟨i', Finset.mem_Iio.mpr (hford i' i hlt), hi'⟩))
  · -- distinctness
    intro j₁ j₂ hj₁1 hj₁k hj₂1 hj₂k hm₁ hm₂ heq
    have h1 : lastNew w (sigma w k) (pos w (sigma w j₁)) = sigma w j₁ :=
      lastNew_arrival hd0 w hj₁1 hj₁k hfin hm₁
    have h2 : lastNew w (sigma w k) (pos w (sigma w j₂)) = sigma w j₂ :=
      lastNew_arrival hd0 w hj₂1 hj₂k hfin hm₂
    rw [heq, h2] at h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := sigma_strict_mono w h (le_trans hj₂k hfin)
      omega
    · have := sigma_strict_mono w h (le_trans hj₁k hfin)
      omega


end ORRW.Support
