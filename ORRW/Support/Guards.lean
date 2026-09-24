/-
Supporting lemmas for the four frozen anti-vacuity guards in `ORRW/Frozen/Guards/`.

Everything here is about the model of `ORRW/Basic.lean` only: the traversed
edges `E` and the range `R`, and the arithmetic of the step rule
`stepWeight`/`totalWeight`/`stepProb`/`prob`.  Nothing in this file is frozen.

The geometry of direction words (`dirVec_ne_zero`, `dirVec_neg`,
`dirVec_eq_or`, `pos_zero`, `pos_succ`, `pos_of_length_le`, `pos_init`) and the
bound `|E_k| ≤ d |R_k|` (`card_edges_le_card_range`) are those of the library
module `LatticeProb.Walk.Path`.  `E` and `R` have the same defining terms as the
library's `pathEdges` and `pathRange`, so each lemma below about them is the
library lemma, restated under the `ORRW` names.
-/
import Mathlib
import LatticeProb.Walk.Path
import ORRW.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open LatticeProb Finset

/-! ### The position process

Encodes `orrw.tex` (`ssec:main-results`): "Let `(X_n)_{n≥0}` be
once-reinforced random walk started at the origin of `ℤ^d`". -/

/-- Every site visited at or before time `k` lies in `R_k`.  Encodes
`orrw.tex`: "The range at time `n` is `R_n := {X_0, …, X_n}`." -/
theorem pos_mem_R {d n : ℕ} (w : Fin n → Dir d) {i k : ℕ} (h : i ≤ k) :
    pos w i ∈ R w k :=
  LatticeProb.pos_mem_pathRange w h

/-- `R_k` always contains the starting site, so it is never empty. -/
theorem R_nonempty {d n : ℕ} (w : Fin n → Dir d) (k : ℕ) : (R w k).Nonempty :=
  LatticeProb.pathRange_nonempty w k

/-- No edge has been crossed at time zero.  Encodes `orrw.tex`
(`ssec:main-results`): "so that `E_0 = ∅`". -/
theorem E_zero {d n : ℕ} (w : Fin n → Dir d) : E w 0 = ∅ :=
  LatticeProb.pathEdges_zero w

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

/-- The traversed-edge set at any time `k ≤ n` is unchanged by dropping the last
letter. -/
theorem E_init {d n : ℕ} (w : Fin (n + 1) → Dir d) {k : ℕ} (hk : k ≤ n) :
    E (Fin.init w) k = E w k :=
  LatticeProb.pathEdges_init w hk

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
    rw [Fin.val_castSucc, stepWeight_init β w (le_of_lt i.isLt),
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
`ℤ^d` on `m` vertices has at most `dm` edges, so `|E_n| ≤ d|R_n|`."  The bound
itself is `LatticeProb.card_edges_le_card_range`. -/

/-- Both endpoints of a traversed edge are visited sites. -/
theorem mem_E_endpoint {d n : ℕ} (w : Fin n → Dir d) {k : ℕ} {e : Sym2 (Site d)}
    (he : e ∈ E w k) {x : Site d} (hx : x ∈ e) : x ∈ R w k :=
  LatticeProb.mem_pathEdges_endpoint w he hx

/-! ### The one-step numeric witness -/

/-- After one step the range is `{0, X_1}` with `X_1 ≠ 0`, so `|R_1| = 2`. -/
theorem card_R_one {d : ℕ} (w : Fin 1 → Dir d) : (R w 1).card = 2 :=
  LatticeProb.card_pathRange_one w

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
