/-
The lazy random walk on `ℤ^d`, and its Green function truncated at `R` steps.

This file supplies the objects that Section 8 of Bou-Rabee--Peres,
*Once-reinforced random walk on `ℤ^d` has range exponent at least `d/(d+1)`*,
states its estimates about.  `orrw.tex`, whose display carries the
label `eq:gR`:

  "Let `P` be the transition operator of simple random walk on `ℤ^d`, let
   `Q := ½(I + P)` be its lazy version, and for an integer `R ≥ 1` put
     `g_R := ∑_{r=0}^{R-1} Q^r(0,·)`,
     `osc(g_R) := max g_R - min g_R`."

Nothing here is frozen and nothing here is probabilistic in Mathlib's sense: the
lazy walk enters the paper only through the three deterministic bounds of
`lem:green` (`orrw.tex`), so it is built as a linear operator on
functions and not as a measure on paths.  `osc` is not defined here; ruling
F-804 of `ORRW/Frozen/Occupation/LazyGreen.lean` states the oscillation bound
pairwise instead, which needs no attainment of `max` or `min`.

Modelling decisions.

* Ruling W-001 (`Q` is an operator, not a matrix).  The paper writes `Q^r(0,x)`
  for the `r`-step transition kernel of the lazy walk.  A kernel on the infinite
  lattice would have to be iterated by an infinite sum, so `Q` is instead the
  one-step operator acting on functions, and `Q^[r] delta0` is the paper's
  `Q^r(0, ·)`.  `ORRW.Q_eq_pushforward` justifies the identification: the `2d`
  unit steps are closed under negation, so averaging a function over the
  neighbours of `x` and pushing a measure forward by one step are literally the
  same operator, and `Q^[r] delta0` is therefore the law of the lazy walk at
  time `r` started from the origin.  Every iterate is a finite sum; no
  summability question arises in the definitions.

* Ruling W-002 (the laziness is `1/2`).  `Q` holds with probability `1/2` and
  otherwise steps to a uniform neighbour, so each of the `2d` neighbours gets
  `1/(4d)`.  This is the walk whose `r`-step kernel has no parity obstruction,
  which is what makes the sup bound `C R^{-d/2}` of `lem:green` true for every
  `R` rather than for every `R` of the right parity.

* Ruling W-003 (`d = 0` is not special-cased).  At `d = 0` the neighbour sum is
  empty and `4 * (d : ℝ) = 0`, so the second term of `Q` is `0 / 0 = 0` and `Q`
  is multiplication by `1/2`.  Nothing below asserts anything false in that
  degenerate case; the statements that need stochasticity carry `0 < d`.
-/
import Mathlib
import ORRW.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

variable {d : ℕ}

/-! ### The lazy step operator -/

/-- One step of the lazy simple random walk on `ℤ^d`, as an operator on
functions: it holds with probability `1/2` and otherwise moves to a uniformly
chosen one of the `2d` neighbours, so

  `(Q f)(x) = (1/2) f(x) + (1/(4d)) ∑_{a} f(x + e_a)`.

Ruling W-001: this is the paper's `Q` read as an operator. -/
noncomputable def Q (f : Site d → ℝ) : Site d → ℝ :=
  fun x => f x / 2 + (∑ a : Dir d, f (x + dirVec a)) / (4 * (d : ℝ))

/-- The point mass at the origin. -/
noncomputable def delta0 : Site d → ℝ := fun x => if x = 0 then 1 else 0

/-- The Green function of the lazy walk truncated at `R` steps:

  `g_R(x) = ∑_{r < R} Q^r(0, x)`.

Ruling W-001 identifies `Q^[r] delta0` with the paper's `Q^r(0, ·)`. -/
noncomputable def gR (R : ℕ) : Site d → ℝ :=
  fun x => ∑ r ∈ range R, Q^[r] (delta0 : Site d → ℝ) x

/-! ### The identification of `Q^[r] delta0` with the law at time `r`

`ORRW.Q_eq_pushforward` is the content of ruling W-001. -/

/-- Flipping the sign bit of a direction negates its unit vector. -/
theorem dirVec_flip (a : Dir d) : dirVec ((a.1, !a.2) : Dir d) = -dirVec a := by
  funext i
  rcases a with ⟨c, b⟩
  simp only [dirVec, Pi.neg_apply]
  cases b <;> split <;> norm_num

/-- The `2d` unit steps are closed under negation, so a sum over the neighbours
`x + e_a` is the same as a sum over the sites `x - e_a` that step to `x`. -/
theorem sum_dirVec_symm (f : Site d → ℝ) (x : Site d) :
    ∑ a : Dir d, f (x - dirVec a) = ∑ a : Dir d, f (x + dirVec a) := by
  have key : ∀ a : Dir d, f (x - dirVec a) = f (x + dirVec ((a.1, !a.2) : Dir d)) := by
    intro a
    rw [dirVec_flip a, ← sub_eq_add_neg]
  have hinv : Function.Involutive (fun a : Dir d => ((a.1, !a.2) : Dir d)) := by
    intro a
    simp
  rw [Finset.sum_congr rfl fun a _ => key a]
  exact Fintype.sum_bijective (fun a : Dir d => ((a.1, !a.2) : Dir d)) hinv.bijective
    _ _ fun a => rfl

/-- `Q` is at the same time the averaging operator over neighbours and the
one-step pushforward of a measure, because the `2d` unit steps are closed under
negation.  Consequently `Q^[r] delta0` is the law of the lazy walk at time `r`
started from the origin, which is the paper's `Q^r(0, ·)` (ruling W-001). -/
theorem Q_eq_pushforward (f : Site d → ℝ) (x : Site d) :
    Q f x = f x / 2 + (∑ a : Dir d, f (x - dirVec a)) / (4 * (d : ℝ)) := by
  rw [Q, sum_dirVec_symm]

/-! ### Guards

These keep the definitions above from being junk: `Q` is a Markov operator, its
iterates are nonnegative, and `gR` is not identically zero. -/

/-- `Q` preserves nonnegativity. -/
theorem Q_nonneg {f : Site d → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Site d) : 0 ≤ Q f x := by
  have h1 : 0 ≤ ∑ a : Dir d, f (x + dirVec a) := Finset.sum_nonneg fun a _ => hf _
  have h2 : (0 : ℝ) ≤ 4 * (d : ℝ) := by positivity
  exact add_nonneg (by linarith [hf x]) (div_nonneg h1 h2)

/-- The row sums of the lazy kernel are `1`: `Q` fixes the constant function
`1`, for every `d ≥ 1`.  This is the stochasticity guard. -/
theorem Q_one (hd : 0 < d) : Q (fun _ : Site d => (1 : ℝ)) = fun _ => 1 := by
  funext x
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [Q]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, mul_one]
  field_simp
  ring

/-- Every iterate of `Q` fixes the constant function `1`. -/
theorem Q_iterate_one (hd : 0 < d) (r : ℕ) :
    Q^[r] (fun _ : Site d => (1 : ℝ)) = fun _ => 1 := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, Q_one hd, ih]

/-- The point mass is nonnegative. -/
theorem delta0_nonneg (x : Site d) : 0 ≤ (delta0 : Site d → ℝ) x := by
  rw [delta0]; split <;> norm_num

/-- Every `r`-step transition probability is nonnegative. -/
theorem iterate_delta0_nonneg (r : ℕ) (x : Site d) :
    0 ≤ Q^[r] (delta0 : Site d → ℝ) x := by
  induction r generalizing x with
  | zero => exact delta0_nonneg x
  | succ r ih => rw [Function.iterate_succ_apply']; exact Q_nonneg (fun y => ih y) x

/-- Laziness alone gives `Q^r(0,0) ≥ 2^{-r}`, so the `r`-step kernel at the
origin is never zero. -/
theorem half_pow_le_iterate_delta0 (r : ℕ) :
    (1 / 2 : ℝ) ^ r ≤ Q^[r] (delta0 : Site d → ℝ) (0 : Site d) := by
  induction r with
  | zero => simp [delta0]
  | succ r ih =>
    rw [Function.iterate_succ_apply', Q]
    have h1 : 0 ≤ ∑ a : Dir d, Q^[r] (delta0 : Site d → ℝ) ((0 : Site d) + dirVec a) :=
      Finset.sum_nonneg fun a _ => iterate_delta0_nonneg r _
    have h2 : (0 : ℝ) ≤ 4 * (d : ℝ) := by positivity
    have h3 := div_nonneg h1 h2
    have h4 : (1 / 2 : ℝ) ^ (r + 1) = (1 / 2 : ℝ) ^ r / 2 := by ring
    rw [h4]
    linarith [ih]

/-- `gR` is nonnegative. -/
theorem gR_nonneg (R : ℕ) (x : Site d) : 0 ≤ gR R x :=
  Finset.sum_nonneg fun r _ => iterate_delta0_nonneg r x

/-- `gR R (0) ≥ 1` for `R ≥ 1`: the truncated Green function is not the zero
function, so the estimates of `lem:green` are not about a degenerate object. -/
theorem one_le_gR_zero {R : ℕ} (hR : 1 ≤ R) : 1 ≤ gR R (0 : Site d) := by
  have h0 : (0 : ℕ) ∈ range R := Finset.mem_range.mpr hR
  have hterm : ∀ r ∈ range R, 0 ≤ Q^[r] (delta0 : Site d → ℝ) (0 : Site d) :=
    fun r _ => iterate_delta0_nonneg r _
  have := Finset.single_le_sum (f := fun r => Q^[r] (delta0 : Site d → ℝ) (0 : Site d))
    hterm h0
  simpa [gR, delta0] using this

/-! ### Finite support

The truncated Green function is supported in the box of radius `R`, so the sum
of `|∇ gR|` over all edges of `ℤ^d`, which the frozen statement asserts to be
summable, has only finitely many nonzero terms. -/

/-- Each coordinate of a unit step is `-1`, `0` or `1`. -/
theorem abs_dirVec_le_one (a : Dir d) (i : Fin d) : |dirVec a i| ≤ 1 := by
  rw [dirVec]
  split <;> [split; skip] <;> norm_num

/-- After `r` steps the lazy walk has moved at most `r` in each coordinate. -/
theorem iterate_delta0_eq_zero {r : ℕ} {x : Site d} {i : Fin d} (h : (r : ℤ) < |x i|) :
    Q^[r] (delta0 : Site d → ℝ) x = 0 := by
  induction r generalizing x with
  | zero =>
    have hx : x ≠ 0 := by
      intro hx0
      rw [hx0] at h
      simp at h
    simp [delta0, hx]
  | succ r ih =>
    have hr : (r : ℤ) < |x i| := by push_cast at h ⊢; omega
    rw [Function.iterate_succ_apply', Q, ih hr]
    have hzero : ∀ a : Dir d, Q^[r] (delta0 : Site d → ℝ) (x + dirVec a) = 0 := by
      intro a
      refine ih ?_
      have hb : |dirVec a i| ≤ 1 := abs_dirVec_le_one a i
      have hcoord : (x + dirVec a) i = x i + dirVec a i := rfl
      have habs : |x i| ≤ |x i + dirVec a i| + |dirVec a i| := by
        simpa using abs_add_le (x i + dirVec a i) (-(dirVec a i))
      rw [hcoord]
      push_cast at h ⊢
      omega
    rw [Finset.sum_congr rfl (fun a _ => hzero a)]
    simp

/-! ### Each undirected edge is named exactly once

Ruling F-805 of `ORRW/Frozen/Occupation/LazyGreen.lean` sums the increments of
`g_R` over `Site d × Fin d`, reading `(x, i)` as the edge `{x, x + e_i}`.  The
two lemmas here are what makes that a sum over the undirected edges of `ℤ^d`
with no edge counted twice and none omitted; the frozen constant `4 d^{3/2} √R`
would be wrong for a parametrization that double counts. -/

/-- Distinct pairs name distinct edges. -/
theorem edgeParam_injective :
    Function.Injective fun p : Site d × Fin d => s(p.1, p.1 + dirVec (p.2, true)) := by
  have hval : ∀ c k : Fin d, dirVec ((c, true) : Dir d) k = if k = c then 1 else 0 := by
    intro c k
    simp [dirVec]
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨hxy, hij⟩ | ⟨hxy, hij⟩
  · have hd : dirVec ((i, true) : Dir d) = dirVec ((j, true) : Dir d) := by
      rw [hxy] at hij
      exact add_left_cancel hij
    have hij' : i = j := by
      by_contra hne
      have h1 := congrFun hd i
      rw [hval i i, hval j i, if_pos rfl, if_neg hne] at h1
      norm_num at h1
    simp only [Prod.mk.injEq]
    exact ⟨hxy, hij'⟩
  · exfalso
    have hsum : dirVec ((j, true) : Dir d) + dirVec ((i, true) : Dir d) = 0 := by
      rw [hxy] at hij
      refine add_left_cancel (a := y) ?_
      rw [add_zero, ← add_assoc]
      exact hij
    have h5 := congrFun hsum i
    rw [Pi.add_apply, Pi.zero_apply, hval i i, if_pos rfl] at h5
    have h6 : (0 : ℤ) ≤ dirVec ((j, true) : Dir d) i := by
      rw [hval j i]
      split <;> norm_num
    omega

/-- Every undirected edge of `ℤ^d` is named by some pair. -/
theorem edgeParam_surjective (x : Site d) (a : Dir d) :
    ∃ p : Site d × Fin d, s(x, x + dirVec a) = s(p.1, p.1 + dirVec (p.2, true)) := by
  rcases a with ⟨c, b⟩
  cases b
  · have hflip : dirVec ((c, false) : Dir d) = -dirVec ((c, true) : Dir d) := by
      have h' : dirVec ((c, true) : Dir d) = -dirVec ((c, false) : Dir d) :=
        dirVec_flip ((c, false) : Dir d)
      rw [h', neg_neg]
    refine ⟨(x + dirVec ((c, false) : Dir d), c), ?_⟩
    rw [hflip, show x + -dirVec ((c, true) : Dir d) + dirVec ((c, true) : Dir d) = x by abel]
    exact Sym2.eq_swap
  · exact ⟨(x, c), rfl⟩

/-- The box of radius `k` in `ℤ^d`, as a `Finset`. -/
def box (d k : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(k : ℤ)) (k : ℤ)

/-- Provides a witness that the box of radius k around the origin does not exhaust the lattice, so the exit-time and resistance arguments always have a site outside to escape to. -/
theorem exists_of_notMem_box {k : ℕ} {x : Site d} (hx : x ∉ box d k) :
    ∃ i : Fin d, (k : ℤ) < |x i| := by
  by_contra hc
  push_neg at hc
  exact hx (Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr (abs_le.mp (hc i)))

/-- `g_R` vanishes outside the box of radius `R`. -/
theorem gR_eq_zero_of_lt {R : ℕ} {x : Site d} {i : Fin d} (h : (R : ℤ) < |x i|) :
    gR R x = 0 := by
  simp only [gR]
  refine Finset.sum_eq_zero fun r hr => iterate_delta0_eq_zero (i := i) ?_
  have hrR : r < R := Finset.mem_range.mp hr
  omega

/-- The family whose sum is the total variation of `g_R` over the edges of
`ℤ^d`, in the parametrization of ruling F-805, is summable: it vanishes off the
finite set `box d (R+1) ×ˢ univ`.  This is what makes the `Summable` conjunct of
`ORRW.Frozen.lazy_green_bounds` a true assertion rather than a hope. -/
theorem summable_gR_gradient (R : ℕ) :
    Summable fun p : Site d × Fin d => |gR R (p.1 + dirVec (p.2, true)) - gR R p.1| := by
  refine summable_of_ne_finset_zero
    (s := box d (R + 1) ×ˢ (Finset.univ : Finset (Fin d))) ?_
  intro p hp
  have hp1 : p.1 ∉ box d (R + 1) := fun h =>
    hp (Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩)
  obtain ⟨j, hj⟩ := exists_of_notMem_box hp1
  have h1 : gR R p.1 = 0 := by
    refine gR_eq_zero_of_lt (i := j) ?_
    push_cast at hj ⊢
    omega
  have h2 : gR R (p.1 + dirVec (p.2, true)) = 0 := by
    refine gR_eq_zero_of_lt (i := j) ?_
    have hb : |dirVec ((p.2, true) : Dir d) j| ≤ 1 := abs_dirVec_le_one _ j
    have hcoord : (p.1 + dirVec ((p.2, true) : Dir d)) j
        = p.1 j + dirVec ((p.2, true) : Dir d) j := rfl
    have habs : |p.1 j| ≤ |p.1 j + dirVec ((p.2, true) : Dir d) j|
        + |dirVec ((p.2, true) : Dir d) j| := by
      simpa using abs_add_le (p.1 j + dirVec ((p.2, true) : Dir d) j)
        (-(dirVec ((p.2, true) : Dir d) j))
    rw [hcoord]
    push_cast at hj ⊢
    omega
  rw [h1, h2]
  norm_num

end ORRW
