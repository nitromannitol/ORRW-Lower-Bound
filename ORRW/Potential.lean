/-
The potential, the charge and the auxiliary processes of Bou-Rabee--Peres,
*Once-reinforced random walk on `ℤ^d` has range exponent at least `d/(d+1)`*,
Section 3, "A potential and a supermartingale" (`sec:potential`),
`orrw.tex`.

The paper's displays, quoted verbatim.

* `orrw.tex`:

    "Let
       `S_n := {x ∈ Z^d : every edge incident to x lies in E_n}`,
       `ν_n := #{y ∼ X_n : {X_n,y} ∉ E_n}`,
       `μ_n := β(2d - ν_n) + ν_n`,
     so that `S_0 = ∅`, `ν_n` counts the untraversed edges at the site the walk
     occupies at step `n`, and `μ_n` is the total weight there, so that
     `μ_n ≤ 2dβ`.  Thus `X_n ∈ S_n` if and only if `ν_n = 0`."

* `orrw.tex`:

    "Let `σ_k := inf{n ≥ 0 : |E_n| = k}`, `σ_0 := 0`, `v_k := X_{σ_k-1}`,
     `w_k := X_{σ_k}`, for every integer `k ≥ 1`, so that `σ_k` is the step at
     which the walk crosses its `k`th distinct edge, `v_k` is the site it
     departs from, and `w_k` the site it arrives at.  Since `|E_n|` increases by
     at most one at each step, `{σ_k ≤ n} = {|E_n| ≥ k}`."  (`eq:sigma-range`)

* `orrw.tex`:

    "Write `η_n := 1_{{|E_n| > |E_{n-1}|}}` for the indicator that the `n`th step
     crosses an untraversed edge."

* `orrw.tex` (`eq:F-def`):

    "The potential is  `Φ_n := 2d u_{S_n}(X_n)`."

* `orrw.tex` (`eq:a-def`):

    "When `ν_n ≥ 1`, so that `X_n ∉ S_n` and `h_{S_n}(X_n)` is defined, put
     `γ_n := 2dβ h_{S_n}(X_n)`, and put `γ_n := 0` when `ν_n = 0`."

* `orrw.tex` (`eq:C-def`):

    "The accumulated charge is
       `Γ_0 := 0`,  `Γ_{n+1} - Γ_n := η_{n+1}(γ_n + Φ_{n+1})`."

Modelling decisions.

* Ruling P-001 (time is an index, the word is the history).  Under ruling R-001
  the sample space at horizon `n` is the finite set of direction words
  `Fin n → Dir d`, so every process of this section is a function of a word `w`
  and a time `k : ℕ`.  Nothing here is a stochastic process in Mathlib's sense
  and no filtration is built: the filtration `(F_n)` of `orrw.tex` is
  carried by the types, since the value of each of these functions at time `k`
  depends on `w` only through its first `k` letters (`ORRW.pos_init`,
  `ORRW.E_init` of `ORRW/Support/Guards.lean`).

* Ruling P-002 (`S` is a `Finset`).  The paper's `S_n` is a subset of the
  infinite lattice, defined by a condition on all `2d` incident edges.  For
  `d ≥ 1` that condition forces `x` to be an endpoint of a traversed edge, hence
  `x ∈ R_k`; `S` is therefore defined as a filter of the `Finset` `R w k`, and
  `ORRW.mem_S_iff` proves that this restriction changes nothing for `d ≥ 1`.

* Ruling P-003 (neighbours are indexed by directions).  `ν_n` counts neighbours
  `y ∼ X_n` with `{X_n, y} ∉ E_n`; since `dirVec` is injective
  (`ORRW.dirVec_injective`), the `2d` neighbours of a site are in bijection with
  `Dir d`, and the count is taken over `Dir d`.  The same reindexing is already
  used in `ORRW.sum_adj_eq_sum_dir` and in `ORRW.Frozen.potential_kernel_exists`.

* Ruling P-004 (`σ_k` uses `≥ k`, and `n + 1` stands for `∞`).  `|E_m|` is
  nondecreasing in `m`, so `inf{m : |E_m| = k}` and `inf{m : |E_m| ≥ k}` agree
  whenever either is finite; the second form is used, so that no unit-increment
  lemma is needed.  Under ruling R-001 the walk has a finite horizon and
  `{m : |E_m| ≥ k}` is empty exactly when `k > |E_n|`, which is the paper's
  `σ_k = ∞`; on that event `sigma` is set to `n + 1`, strictly beyond the
  horizon.  The junk value `0` that `Nat.sInf` would supply is thereby excluded,
  and `ORRW.sigma_le_iff` is the paper's `eq:sigma-range`.

* Ruling P-005 (`η_0 = 0`).  `η_n` is defined in the paper only for `n ≥ 1`.
  The definition below uses truncated subtraction, so `η_0` compares `|E_0|`
  with itself and is `0`; `Γ` never reads `η_0`.

* Ruling P-006 (`μ` is the step-rule normalizer).  `mu` is defined by the
  paper's formula `β(2d - ν_k) + ν_k`, and `ORRW.mu_eq_totalWeight` proves that
  it equals `ORRW.totalWeight`, the denominator of the step rule of
  `ORRW/Basic.lean`.  That identity is what makes the weighted averages of
  Section 3 and Section 5 genuine averages.
-/
import ORRW.Lattice
import ORRW.Support.Guards

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

variable {d n : ℕ}

/-! ### Saturated sites, untraversed edges, and the total weight -/

/-- `S w k`: the set of sites all of whose incident edges are traversed by time
`k`, `orrw.tex`:

  "`S_n := {x ∈ Z^d : every edge incident to x lies in E_n}`".

Realized as a `Finset` by filtering the range `R w k` (ruling P-002); for
`d ≥ 1` this is the same set, by `ORRW.mem_S_iff`. -/
def S (w : Fin n → Dir d) (k : ℕ) : Finset (Site d) :=
  (R w k).filter (fun x => ∀ a : Dir d, s(x, x + dirVec a) ∈ E w k)

/-- `nu w k`: the number of untraversed edges at the site the walk occupies at
time `k`, `orrw.tex`:

  "`ν_n := #{y ∼ X_n : {X_n,y} ∉ E_n}`".

Counted over directions (ruling P-003). -/
def nu (w : Fin n → Dir d) (k : ℕ) : ℕ :=
  (univ.filter (fun a : Dir d => s(pos w k, pos w k + dirVec a) ∉ E w k)).card

/-- `mu β w k`: the total weight at the site the walk occupies at time `k`,
`orrw.tex`:

  "`μ_n := β(2d - ν_n) + ν_n`". -/
def mu (β : ℝ) (w : Fin n → Dir d) (k : ℕ) : ℝ :=
  β * (2 * (d : ℝ) - (nu w k : ℝ)) + (nu w k : ℝ)

/-- `sigma w k`: the step at which the walk crosses its `k`th distinct edge,
`orrw.tex`:

  "`σ_k := inf{n ≥ 0 : |E_n| = k}`, `σ_0 := 0`, ... `σ_k` is the step at which
   the walk crosses its `k`th distinct edge".

Ruling P-004: the infimum is taken over `{m : |E_m| ≥ k}`, and the paper's
`σ_k = ∞` is recorded as `n + 1`, one step beyond the horizon. -/
noncomputable def sigma (w : Fin n → Dir d) (k : ℕ) : ℕ :=
  if k ≤ (E w n).card then sInf {m : ℕ | k ≤ (E w m).card} else n + 1

/-- `eta w k`: the indicator that the `k`th step crosses an untraversed edge,
`orrw.tex`:

  "Write `η_n := 1_{{|E_n| > |E_{n-1}|}}` for the indicator that the `n`th step
   crosses an untraversed edge". -/
def eta (w : Fin n → Dir d) (k : ℕ) : ℝ :=
  if (E w (k - 1)).card < (E w k).card then 1 else 0

/-! ### The potential and the charge -/

/-- `Phi w k`: the potential, `orrw.tex` (`eq:F-def`):

  "The potential is  `Φ_n := 2d u_{S_n}(X_n)`." -/
noncomputable def Phi (w : Fin n → Dir d) (k : ℕ) : ℝ :=
  2 * (d : ℝ) * u (S w k) (pos w k)

/-- `gamma β w k`: the charge rate, `orrw.tex` (`eq:a-def`):

  "When `ν_n ≥ 1`, so that `X_n ∉ S_n` and `h_{S_n}(X_n)` is defined, put
   `γ_n := 2dβ h_{S_n}(X_n)`, and put `γ_n := 0` when `ν_n = 0`." -/
noncomputable def gamma (β : ℝ) (w : Fin n → Dir d) (k : ℕ) : ℝ :=
  if nu w k = 0 then 0 else 2 * (d : ℝ) * β * h (S w k) (pos w k)

/-- `Gamma β w k`: the accumulated charge, `orrw.tex` (`eq:C-def`):

  "The accumulated charge is
     `Γ_0 := 0`,  `Γ_{n+1} - Γ_n := η_{n+1}(γ_n + Φ_{n+1})`." -/
noncomputable def Gamma (β : ℝ) (w : Fin n → Dir d) : ℕ → ℝ
  | 0 => 0
  | k + 1 => Gamma β w k + eta w (k + 1) * (gamma β w k + Phi w (k + 1))

/-! ### Basic properties

None of this is frozen; it is what keeps the definitions above from being junk. -/

/-- The traversed-edge set grows with time. -/
theorem E_mono (w : Fin n → Dir d) {j k : ℕ} (hjk : j ≤ k) : E w j ⊆ E w k := by
  unfold E
  refine Finset.image_subset_image ?_
  exact Finset.range_subset_range.mpr (min_le_min hjk (le_refl n))

/-- The number of traversed edges is nondecreasing in time. -/
theorem card_E_mono (w : Fin n → Dir d) {j k : ℕ} (hjk : j ≤ k) :
    (E w j).card ≤ (E w k).card :=
  Finset.card_le_card (E_mono w hjk)

/-- For `d ≥ 1` the restriction of `S` to the range in ruling P-002 loses
nothing: `S w k` is exactly the set of sites all of whose incident edges are
traversed by time `k`. -/
theorem mem_S_iff (hd : 0 < d) (w : Fin n → Dir d) (k : ℕ) (x : Site d) :
    x ∈ S w k ↔ ∀ a : Dir d, s(x, x + dirVec a) ∈ E w k := by
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    refine Finset.mem_filter.mpr ⟨?_, hx⟩
    exact mem_E_endpoint w (hx (⟨0, hd⟩, true)) (Sym2.mem_mk_left _ _)

/-- `S_0 = ∅`, `orrw.tex`. -/
theorem S_zero (hd : 0 < d) (w : Fin n → Dir d) : S w 0 = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have hmem := (mem_S_iff hd w 0 x).mp hx (⟨0, hd⟩, true)
  rw [E_zero] at hmem
  exact absurd hmem (Finset.notMem_empty _)

/-- "Thus `X_n ∈ S_n` if and only if `ν_n = 0`", `orrw.tex`. -/
theorem nu_eq_zero_iff (hd : 0 < d) (w : Fin n → Dir d) (k : ℕ) :
    nu w k = 0 ↔ pos w k ∈ S w k := by
  rw [nu, Finset.card_eq_zero, Finset.filter_eq_empty_iff, mem_S_iff hd]
  simp

/-- The paper's `μ_n` is the denominator of the step rule of `ORRW/Basic.lean`
(ruling P-006). -/
theorem mu_eq_totalWeight (β : ℝ) (w : Fin n → Dir d) (k : ℕ) :
    mu β w k = totalWeight β w k := by
  have hsplit :
      (univ.filter fun a : Dir d => s(pos w k, pos w k + dirVec a) ∈ E w k).card
        + (univ.filter fun a : Dir d => s(pos w k, pos w k + dirVec a) ∉ E w k).card
        = 2 * d := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  have hsum : totalWeight β w k
      = ((univ.filter fun a : Dir d => s(pos w k, pos w k + dirVec a) ∈ E w k).card : ℝ) * β
        + ((univ.filter fun a : Dir d => s(pos w k, pos w k + dirVec a) ∉ E w k).card : ℝ) := by
    unfold totalWeight stepWeight
    rw [Finset.sum_ite]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hcast := congrArg (fun m : ℕ => (m : ℝ)) hsplit
  push_cast at hcast
  have hcast' :
      ((univ.filter fun a : Dir d => s(pos w k, pos w k + dirVec a) ∈ E w k).card : ℝ)
        = 2 * (d : ℝ)
          - ((univ.filter fun a : Dir d => s(pos w k, pos w k + dirVec a) ∉ E w k).card : ℝ) := by
    linarith
  rw [hsum, mu, nu, hcast']
  ring

/-- `σ_0 = 0`, `orrw.tex`. -/
theorem sigma_zero (w : Fin n → Dir d) : sigma w 0 = 0 := by
  unfold sigma
  rw [if_pos (Nat.zero_le _)]
  exact Nat.sInf_eq_zero.mpr (Or.inl (by simp))

/-- `{σ_k ≤ m} = {|E_m| ≥ k}`, `orrw.tex` (`eq:sigma-range`), for every
time `m` within the horizon. -/
theorem sigma_le_iff (w : Fin n → Dir d) {k m : ℕ} (hm : m ≤ n) :
    sigma w k ≤ m ↔ k ≤ (E w m).card := by
  unfold sigma
  constructor
  · intro hσ
    by_cases hk : k ≤ (E w n).card
    · rw [if_pos hk] at hσ
      have hne : ∃ j, j ∈ {j : ℕ | k ≤ (E w j).card} := ⟨n, hk⟩
      have hmem : sInf {j : ℕ | k ≤ (E w j).card} ∈ {j : ℕ | k ≤ (E w j).card} :=
        Nat.sInf_mem hne
      exact le_trans hmem (card_E_mono w hσ)
    · rw [if_neg hk] at hσ
      omega
  · intro hk
    have hkn : k ≤ (E w n).card := le_trans hk (card_E_mono w hm)
    rw [if_pos hkn]
    exact Nat.sInf_le hk

end ORRW
