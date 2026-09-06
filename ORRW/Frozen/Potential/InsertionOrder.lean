/-
Frozen statement of Lemma 3.2 of Bou-Rabee--Peres, *Once-reinforced random walk
on `ℤ^d` has range exponent at least `d/(d+1)`*, Section 3, Lemma
(Ordering the visited sites), label `lem:walk-order`, `orrw.tex:726-738`:

  "Let `k ≥ 1` be an integer, and work on the event `{σ_k < ∞}`.  Put
   `V := R_{σ_k}` and `M := |V|`.  Then `M ≤ k+1`, and there is an ordering
   `x_1, …, x_M` of `V` for which the sets `A_i := {x_1, …, x_i}` satisfy the
   following for every `1 ≤ j ≤ k`.
     (i) If `v_j = x_i`, then `S_{σ_{j-1}} ⊆ A_{i-1}`.
     (ii) If `w_j ∈ S_{σ_j}` and `w_j = x_i`, then `S_{σ_j} ⊆ A_i`.  The sites
     `w_j` satisfying `w_j ∈ S_{σ_j}` are distinct."

Here `v_j = X_{σ_j - 1}` and `w_j = X_{σ_j}` (`orrw.tex`); they are
written below as `pos w (sigma w j - 1)` and `pos w (sigma w j)`, where `w` is
the direction word, not the paper's arrival site.

Modelling decisions.

* Ruling F-511 (the event `{σ_k < ∞}`).  Under ruling R-001 the walk has the
  finite horizon `n` and `ORRW.sigma` records the paper's `σ_k = ∞` as `n + 1`
  (ruling P-004).  The paper's event `{σ_k < ∞}` is therefore the hypothesis
  `k ≤ (E w n).card`, which by `ORRW.sigma_le_iff` (the paper's
  `eq:sigma-range`) is exactly `σ_k ≤ n`.

* Ruling F-512 (the ordering).  As in `ResistancePacking.lean` (ruling F-301)
  and `InsertionInequality.lean` (ruling F-401), an ordering `x_1, …, x_M` of a
  finite set is an injective `x : Fin M → Site d` whose image is that set, with
  `M` the cardinality of `V`.  For the `0`-indexed step `i : Fin M`, the paper's
  `A_{i-1}` is `(Finset.Iio i).image x` and the paper's `A_i` is
  `insert (x i) ((Finset.Iio i).image x)`.  The same reading is used here, so
  that the conclusion feeds `lem:insertion` verbatim.

* Ruling F-513 (`M ≤ k + 1` is not part of the existential).  The cardinality
  bound does not mention the ordering, so it is a separate conjunct.

* Ruling F-514 (the distinctness clause).  "The sites `w_j` satisfying
  `w_j ∈ S_{σ_j}` are distinct" is rendered as injectivity of `j ↦ X_{σ_j}` on
  the set of indices `1 ≤ j ≤ k` with `X_{σ_j} ∈ S_{σ_j}`.

* Ruling F-516 (truncated subtraction).  `sigma w j - 1` and `j - 1` are
  natural subtractions.  Both are the intended values on the stated range: for
  `j ≥ 1` the paper's `σ_j ≥ 1`, because `|E_0| = 0 < 1 ≤ j`, and `σ_0 = 0`
  (`ORRW.sigma_zero`), so `S_{σ_{j-1}}` at `j = 1` is `S_0 = ∅`
  (`ORRW.S_zero`).

* Ruling F-515 (`d ≥ 1`).  The lemma is stated in the paper inside a section
  fixing `d ≥ 2`, but its proof uses only that the walk is a walk.  `1 ≤ d` is
  assumed because it is what makes `ORRW.S` faithful (ruling P-002); it does not
  force the conclusion.
-/
import ORRW.Potential
import ORRW.Support.WalkOrder

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.insertion_order {d n : ℕ} (hd : 1 ≤ d) (w : Fin n → Dir d)
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
            pos w (sigma w j₁) = pos w (sigma w j₂) → j₁ = j₂)
-- FROZEN-STATEMENT-END
:= ORRW.Support.insertion_order_of hd w k hk hfin
