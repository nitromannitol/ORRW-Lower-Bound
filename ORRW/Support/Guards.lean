/-
Supporting lemmas for the four frozen anti-vacuity guards in `ORRW/Frozen/Guards/`.

Everything here is about the model of `ORRW/Basic.lean` only: the geometry of
`dirVec`, `pos`, `edgeAt`, `E` and `R`, and the arithmetic of the step rule
`stepWeight`/`totalWeight`/`stepProb`/`prob`.  Nothing in this file is frozen.
-/
import Mathlib
import ORRW.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

/-! ### Direction vectors -/

/-- A direction vector is a unit coordinate vector, hence never zero.  A term of
`Dir d` carries a coordinate `a.1 : Fin d`, so no `0 < d` hypothesis is needed. -/
theorem dirVec_ne_zero {d : ℕ} (a : Dir d) : dirVec a ≠ 0 := by
  intro h
  have h' : dirVec a a.1 = (0 : Fin d → ℤ) a.1 := by rw [h]
  simp [dirVec] at h'
  split at h' <;> norm_num at h'

/-- The two signs of one coordinate give opposite vectors. -/
theorem dirVec_neg {d : ℕ} (c : Fin d) :
    dirVec ((c, false) : Dir d) = -dirVec ((c, true) : Dir d) := by
  funext j
  simp only [dirVec, Pi.neg_apply]
  split <;> norm_num

/-- Every direction vector is `± e_i` for its own coordinate `i`. -/
theorem dirVec_eq_or {d : ℕ} (a : Dir d) :
    dirVec a = dirVec ((a.1, true) : Dir d) ∨ dirVec a = -dirVec ((a.1, true) : Dir d) := by
  rcases a with ⟨c, b⟩
  cases b
  · exact Or.inr (dirVec_neg c)
  · exact Or.inl rfl

/-! ### The position process

Encodes `orrw.tex` (`ssec:main-results`): "Let `(X_n)_{n≥0}` be
once-reinforced random walk started at the origin of `ℤ^d`". -/

/-- The walk starts at the origin: `X_0 = 0`. -/
theorem pos_zero {d n : ℕ} (w : Fin n → Dir d) : pos w 0 = 0 := by
  simp [pos]

/-- One step of the walk moves by the direction vector of the letter just read:
`X_{i+1} = X_i + dirVec (w i)` for `i < n`. -/
theorem pos_succ {d n : ℕ} (w : Fin n → Dir d) (i : ℕ) (hi : i < n) :
    pos w (i + 1) = pos w i + dirVec (w ⟨i, hi⟩) := by
  have key : ∀ t : Fin n, (if (t : ℕ) < i + 1 then dirVec (w t) else 0)
      = (if (t : ℕ) < i then dirVec (w t) else 0)
        + (if t = (⟨i, hi⟩ : Fin n) then dirVec (w t) else 0) := by
    intro t
    by_cases h1 : (t : ℕ) < i
    · have h2 : t ≠ (⟨i, hi⟩ : Fin n) := by
        intro h; rw [h] at h1; simp at h1
      simp [h1, Nat.lt_succ_of_lt h1, h2]
    · by_cases h2 : (t : ℕ) = i
      · have h3 : t = (⟨i, hi⟩ : Fin n) := Fin.ext h2
        simp [h3]
      · have h4 : ¬ ((t : ℕ) < i + 1) := by omega
        have h5 : t ≠ (⟨i, hi⟩ : Fin n) := fun h => h2 (by rw [h])
        simp [h1, h4, h5]
  unfold pos
  rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => key t), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (⟨i, hi⟩ : Fin n) (fun t => dirVec (w t))]
  simp

/-- Past the length of the word the position is frozen at the total displacement.
This is an artefact of the finite-horizon model of `ORRW/Basic.lean`; the paper's
walk is never evaluated past time `n`. -/
theorem pos_of_length_le {d n : ℕ} (w : Fin n → Dir d) {k : ℕ} (hk : n ≤ k) :
    pos w k = ∑ t : Fin n, dirVec (w t) :=
  Finset.sum_congr rfl fun t _ => if_pos (lt_of_lt_of_le t.isLt hk)

/-- Every site visited at or before time `k` lies in `R_k`.  Encodes
`orrw.tex`: "The range at time `n` is `R_n := {X_0, …, X_n}`." -/
theorem pos_mem_R {d n : ℕ} (w : Fin n → Dir d) {i k : ℕ} (h : i ≤ k) :
    pos w i ∈ R w k :=
  mem_image_of_mem (pos w) (mem_range.mpr (by omega))

/-- `R_k` always contains the starting site, so it is never empty. -/
theorem R_nonempty {d n : ℕ} (w : Fin n → Dir d) (k : ℕ) : (R w k).Nonempty :=
  ⟨pos w 0, pos_mem_R w (Nat.zero_le k)⟩

/-- No edge has been crossed at time zero.  Encodes `orrw.tex`
(`ssec:main-results`): "so that `E_0 = ∅`". -/
theorem E_zero {d n : ℕ} (w : Fin n → Dir d) : E w 0 = ∅ := by
  simp [E]

/-! ### The step rule -/

/-- Each incident weight is `β` or `1`, so it is at least `1` when `1 ≤ β`.
Encodes `orrw.tex` (`ssec:main-results`): "the walk steps from `X_n` to a
neighbor `y` with probability proportional to `β` if `{X_n, y} ∈ E_n` and
proportional to `1` otherwise." -/
theorem one_le_stepWeight {d n : ℕ} {β : ℝ} (hβ : 1 ≤ β) (w : Fin n → Dir d)
    (k : ℕ) (a : Dir d) : 1 ≤ stepWeight β w k a := by
  unfold stepWeight
  split
  · exact hβ
  · exact le_refl 1

/-- Each incident weight is strictly positive when `1 ≤ β`. -/
theorem stepWeight_pos {d n : ℕ} {β : ℝ} (hβ : 1 ≤ β) (w : Fin n → Dir d)
    (k : ℕ) (a : Dir d) : 0 < stepWeight β w k a := by
  linarith [one_le_stepWeight hβ w k a]

/-- The denominator of the step rule never vanishes: it is a sum of `2d`
positive terms. -/
theorem totalWeight_pos {d n : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β)
    (w : Fin n → Dir d) (k : ℕ) : 0 < totalWeight β w k :=
  Finset.sum_pos (fun a _ => stepWeight_pos hβ w k a)
    ⟨(⟨0, hd⟩, true), Finset.mem_univ _⟩

/-- At time zero no edge is traversed, so all `2d` incident weights are `1` and
the normalizer is exactly `2d`, for every `β`. -/
theorem totalWeight_zero {d n : ℕ} (β : ℝ) (w : Fin n → Dir d) :
    totalWeight β w 0 = 2 * d := by
  unfold totalWeight stepWeight
  rw [E_zero]
  simp only [Finset.notMem_empty, if_false]
  rw [Finset.sum_const]
  simp only [Finset.card_univ]
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-! ### The step rule depends on the word only through the past

`pos w k`, `E w k`, `stepWeight β w k` and `totalWeight β w k` are determined by
the letters `w 0, …, w (k-1)`.  The form used below is that dropping the last
letter of a word of length `n + 1` changes none of them at any time `k ≤ n`. -/

/-- The position at any time `k ≤ n` is unchanged by dropping the last letter. -/
theorem pos_init {d n : ℕ} (w : Fin (n + 1) → Dir d) {k : ℕ} (hk : k ≤ n) :
    pos (Fin.init w) k = pos w k := by
  unfold pos
  rw [Fin.sum_univ_castSucc]
  simp [Fin.init, Fin.val_last, Nat.not_lt.mpr hk]

/-- The traversed-edge set at any time `k ≤ n` is unchanged by dropping the last
letter. -/
theorem E_init {d n : ℕ} (w : Fin (n + 1) → Dir d) {k : ℕ} (hk : k ≤ n) :
    E (Fin.init w) k = E w k := by
  unfold E
  rw [Nat.min_eq_left hk, Nat.min_eq_left (by omega : k ≤ n + 1)]
  refine Finset.image_congr ?_
  intro i hi
  have hik : i < k := Finset.mem_range.mp (Finset.mem_coe.mp hi)
  unfold edgeAt
  rw [pos_init w (by omega : i ≤ n), pos_init w (by omega : i + 1 ≤ n)]

/-- The incident weights at any time `k ≤ n` are unchanged by dropping the last
letter. -/
theorem stepWeight_init {d n : ℕ} (β : ℝ) (w : Fin (n + 1) → Dir d) {k : ℕ} (hk : k ≤ n)
    (a : Dir d) : stepWeight β (Fin.init w) k a = stepWeight β w k a := by
  unfold stepWeight
  rw [pos_init w hk, E_init w hk]

/-- The normalizer at any time `k ≤ n` is unchanged by dropping the last letter. -/
theorem totalWeight_init {d n : ℕ} (β : ℝ) (w : Fin (n + 1) → Dir d) {k : ℕ} (hk : k ≤ n) :
    totalWeight β (Fin.init w) k = totalWeight β w k :=
  Finset.sum_congr rfl fun a _ => stepWeight_init β w hk a

/-- The law of a word of length `n + 1` factors as the law of its first `n`
letters times the conditional probability of the last step. -/
theorem prob_succ {d n : ℕ} (β : ℝ) (w : Fin (n + 1) → Dir d) :
    prob β w
      = prob β (Fin.init w)
        * (stepWeight β (Fin.init w) n (w (Fin.last n)) / totalWeight β (Fin.init w) n) := by
  unfold prob
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    unfold stepProb
    rw [Fin.coe_castSucc, stepWeight_init β w (le_of_lt i.isLt),
      totalWeight_init β w (le_of_lt i.isLt)]
    rfl
  · unfold stepProb
    rw [Fin.val_last, stepWeight_init β w (le_refl n), totalWeight_init β w (le_refl n)]

/-- Summing the last letter out of the law of a word of length `n + 1` returns
the law of its first `n` letters: the innermost normalization identity
`∑_a stepWeight / totalWeight = 1`. -/
theorem sum_prob_snoc {d n : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) (v : Fin n → Dir d) :
    ∑ a : Dir d, prob β (Fin.snoc v a) = prob β v := by
  have hne : totalWeight β v n ≠ 0 := ne_of_gt (totalWeight_pos hd hβ v n)
  have hstep : ∀ a : Dir d, prob β (Fin.snoc v a)
      = prob β v * (stepWeight β v n a / totalWeight β v n) := by
    intro a
    rw [prob_succ β (Fin.snoc v a), Fin.init_snoc, Fin.snoc_last]
  rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.mul_sum, ← Finset.sum_div]
  have hsum : (∑ a : Dir d, stepWeight β v n a) = totalWeight β v n := rfl
  rw [hsum, div_self hne, mul_one]

/-- `prob` is a probability mass function on direction words: total mass one. -/
theorem sum_prob_eq_one {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) (n : ℕ) :
    ∑ w : Fin n → Dir d, prob β w = 1 := by
  induction n with
  | zero => simp [prob]
  | succ n ih =>
    have key : ∑ w : Fin (n + 1) → Dir d, prob β w
        = ∑ p : Dir d × (Fin n → Dir d), prob β (Fin.snoc p.2 p.1) :=
      (Fintype.sum_equiv (Fin.snocEquiv (fun _ => Dir d))
        (fun p => prob β (Fin.snoc p.2 p.1)) (fun w => prob β w) (fun _ => rfl)).symm
    rw [key, Fintype.sum_prod_type, Finset.sum_comm,
      Finset.sum_congr rfl (fun v _ => sum_prob_snoc hd hβ v), ih]

/-! ### Traversed edges versus visited sites

Encodes `orrw.tex` (equation `eq:edges-sites`): "Every subgraph of
`ℤ^d` on `m` vertices has at most `dm` edges, so `|E_n| ≤ d|R_n|`." -/

/-- Both endpoints of a traversed edge are visited sites. -/
theorem mem_E_endpoint {d n : ℕ} (w : Fin n → Dir d) {k : ℕ} {e : Sym2 (Site d)}
    (he : e ∈ E w k) {x : Site d} (hx : x ∈ e) : x ∈ R w k := by
  rw [E, Finset.mem_image] at he
  obtain ⟨i, hi, rfl⟩ := he
  have hik : i < min k n := Finset.mem_range.mp hi
  rw [edgeAt, Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · exact pos_mem_R w (by omega)
  · exact pos_mem_R w (by omega)

/-- The positive-direction parametrization of the edges of `ℤ^d`: a site
together with a coordinate.  Each edge of `ℤ^d` is `edgeOf (y, c)` for exactly
one pair, namely its endpoint `y` with the smaller `c`-th coordinate. -/
def edgeOf {d : ℕ} (p : Site d × Fin d) : Sym2 (Site d) :=
  s(p.1, p.1 + dirVec (p.2, true))

/-- Every edge crossed at a time `i` that is a genuine step (`i < n`) is
`edgeOf (y, c)` for a visited site `y` and a coordinate `c`. -/
theorem edgeAt_eq_edgeOf {d n : ℕ} (w : Fin n → Dir d) {i k : ℕ} (hi : i < n) (hik : i < k) :
    ∃ y c, y ∈ R w k ∧ edgeAt w i = edgeOf (y, c) := by
  have hstep : pos w (i + 1) = pos w i + dirVec (w ⟨i, hi⟩) := pos_succ w i hi
  rcases dirVec_eq_or (w ⟨i, hi⟩) with h | h
  · refine ⟨pos w i, (w ⟨i, hi⟩).1, pos_mem_R w (by omega), ?_⟩
    rw [edgeAt, edgeOf, hstep, h]
  · refine ⟨pos w (i + 1), (w ⟨i, hi⟩).1, pos_mem_R w (by omega), ?_⟩
    have h2 : pos w (i + 1) + dirVec (((w ⟨i, hi⟩).1, true) : Dir d) = pos w i := by
      rw [hstep, h]; abel
    rw [edgeAt, edgeOf]
    simp only [h2]
    exact Sym2.eq_swap

/-- `|E_k| ≤ d |R_k|`.  Encodes `orrw.tex` (equation `eq:edges-sites`):
"Every subgraph of `ℤ^d` on `m` vertices has at most `dm` edges, so
`|E_n| ≤ d|R_n|`."

The proof is the injection `e ↦ (lower endpoint, coordinate)` of `E_k` into
`R_k × Fin d`.  Every index `i` contributing to `E w k` satisfies `i < min k n`,
hence both `i < n` (so step `i` is a genuine step and `edgeAt w i` is a real edge
of `ℤ^d`, not a loop) and `i < k` (so both its endpoints lie in `R_k`).

No `0 < d` hypothesis is needed.  At `d = 0` the argument is vacuous rather than
special: `i < n` forces `Fin n` to be inhabited, so `w` supplies a term of
`Dir 0 = Fin 0 × Bool`, and the coordinate it names is the `c : Fin d` the
injection asks for.  This is why `E` must be cut off at
`min k n` for this to be true at all. -/
theorem card_edges_le_card_range {d n : ℕ} (w : Fin n → Dir d) (k : ℕ) :
    (E w k).card ≤ d * (R w k).card := by
  classical
  have hsub : E w k ⊆ ((R w k) ×ˢ (univ : Finset (Fin d))).image edgeOf := by
    intro e he
    rw [E, Finset.mem_image] at he
    obtain ⟨i, hi, rfl⟩ := he
    have hik : i < min k n := Finset.mem_range.mp hi
    obtain ⟨y, c, hy, hyc⟩ := edgeAt_eq_edgeOf w (by omega : i < n) (by omega : i < k)
    exact Finset.mem_image.mpr ⟨(y, c), Finset.mem_product.mpr ⟨hy, Finset.mem_univ _⟩, hyc.symm⟩
  calc (E w k).card
      ≤ (((R w k) ×ˢ (univ : Finset (Fin d))).image edgeOf).card := Finset.card_le_card hsub
    _ ≤ ((R w k) ×ˢ (univ : Finset (Fin d))).card := Finset.card_image_le
    _ = (R w k).card * d := by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ = d * (R w k).card := Nat.mul_comm _ _

/-! ### The one-step numeric witness -/

/-- After one step the range is `{0, X_1}` with `X_1 ≠ 0`, so `|R_1| = 2`. -/
theorem card_R_one {d : ℕ} (w : Fin 1 → Dir d) : (R w 1).card = 2 := by
  classical
  have h1 : pos w 1 = dirVec (w 0) := by
    have h := pos_succ w 0 (by omega : (0 : ℕ) < 1)
    rw [pos_zero] at h
    simpa using h
  have hne : pos w 0 ≠ pos w 1 := by
    rw [pos_zero, h1]
    exact fun h => dirVec_ne_zero (w 0) h.symm
  have hR : R w 1 = {pos w 0, pos w 1} := by
    unfold R
    rw [show (Finset.range 2 : Finset ℕ) = {0, 1} from by decide]
    rw [Finset.image_insert, Finset.image_singleton]
  rw [hR, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

/-- One step from the origin has crossed no edge, so all `2d` incident weights
are `1` and every one-letter word has probability `1/(2d)`, for every `β`. -/
theorem prob_one_step {d : ℕ} (β : ℝ) (w : Fin 1 → Dir d) :
    prob β w = 1 / (2 * d) := by
  have hw : stepWeight β w 0 (w 0) = 1 := by
    unfold stepWeight
    rw [E_zero]
    simp
  have hprob : prob β w = stepWeight β w 0 (w 0) / totalWeight β w 0 := by
    unfold prob stepProb
    rw [Fin.prod_univ_one]
    norm_num
  rw [hprob, hw, totalWeight_zero β w]

/-- The expected range after one step of the two-dimensional walk is exactly `2`,
for every `β`: four equally likely directions, each giving `|R_1| = 2`. -/
theorem expect_card_range_one_step (β : ℝ) :
    expect (d := 2) 1 β (fun w => ((R w 1).card : ℝ)) = 2 := by
  unfold expect
  have hterm : ∀ w : Fin 1 → Dir 2, prob β w * ((R w 1).card : ℝ) = 1 / 2 := by
    intro w
    rw [prob_one_step β w, card_R_one w]
    norm_num
  rw [Finset.sum_congr rfl (fun w (_ : w ∈ Finset.univ) => hterm w), Finset.sum_const,
    Finset.card_univ]
  simp
  norm_num

end ORRW
