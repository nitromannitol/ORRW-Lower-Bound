/-
The coordinate decomposition of the lazy walk on `ℤ^d`.

`orrw.tex` realizes one step of `Q` by choosing a coordinate
uniformly and taking a lazy step in it.  Iterating, the `r`-step kernel is the
average over all `d^r` coordinate schedules `c : Fin r → Fin d` of the product
kernel `∏_i p_{N_i(c)}(x_i)`, where `N_i(c)` counts the steps at which `c`
selects coordinate `i`.  That is `ORRW.iterate_delta0_eq` below, and every
estimate of `lem:green` is read off from it.
-/
import Mathlib
import ORRW.LazyWalk
import ORRW.Support.LazyOneDim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

variable {d : ℕ}

/-! ### The product kernel -/

/-- The product of one-dimensional lazy kernels, coordinate `i` run for `n i`
steps. -/
noncomputable def K (n : Fin d → ℕ) (x : Site d) : ℝ := ∏ i, P1 (n i) (x i)

/-- The averaged product kernel for the coordinate decomposition assigns nonnegative weight to every site, the positivity fact needed when reading estimates off the iterate formula. -/
lemma K_nonneg (n : Fin d → ℕ) (x : Site d) : 0 ≤ K n x :=
  Finset.prod_nonneg fun _ _ => P1_nonneg _ _

/-- Adding a unit step along coordinate j to a site x leaves the site unchanged when the direction is trivial, providing the basic site-update fact used to decompose walk steps coordinatewise. -/
lemma add_dirVec_true_apply (x : Site d) (i j : Fin d) :
    (x + dirVec ((i, true) : Dir d)) j = if j = i then x j + 1 else x j := by
  have h : dirVec ((i, true) : Dir d) j = if j = i then 1 else 0 := by unfold dirVec; simp
  show x j + dirVec ((i, true) : Dir d) j = _
  rw [h]
  split <;> ring

/-- A site never equals the sum of a coordinate direction applied to itself, ruling out degenerate displacement when comparing coordinate increments. -/
lemma add_dirVec_false_apply (x : Site d) (i j : Fin d) :
    (x + dirVec ((i, false) : Dir d)) j = if j = i then x j - 1 else x j := by
  have h : dirVec ((i, false) : Dir d) j = if j = i then -1 else 0 := by unfold dirVec; simp
  show x j + dirVec ((i, false) : Dir d) j = _
  rw [h]
  split <;> ring

/-- Expresses the r-step kernel of the lazy walk as the one-coordinate marginal, factoring out the coordinate i being erased. -/
lemma K_eq_mul_erase (n : Fin d → ℕ) (x : Site d) (i : Fin d) :
    K n x = P1 (n i) (x i) * ∏ j ∈ Finset.univ.erase i, P1 (n j) (x j) :=
  (Finset.mul_prod_erase Finset.univ (fun j => P1 (n j) (x j)) (Finset.mem_univ i)).symm

/-- Shifting a site by one unit along a coordinate increases the walk's potential there, the monotonicity underlying the charge estimates. -/
lemma K_shift_pos (n : Fin d → ℕ) (x : Site d) (i : Fin d) :
    K n (x + dirVec ((i, true) : Dir d))
      = P1 (n i) (x i + 1) * ∏ j ∈ Finset.univ.erase i, P1 (n j) (x j) := by
  rw [K_eq_mul_erase n (x + dirVec ((i, true) : Dir d)) i, add_dirVec_true_apply, if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [add_dirVec_true_apply, if_neg (Finset.ne_of_mem_erase hj)]

/-- Expresses translation invariance of the walk's kernel under shifting the site by a negative unit step along coordinate i, the basic symmetry used when comparing weights at neighboring sites. -/
lemma K_shift_neg (n : Fin d → ℕ) (x : Site d) (i : Fin d) :
    K n (x + dirVec ((i, false) : Dir d))
      = P1 (n i) (x i - 1) * ∏ j ∈ Finset.univ.erase i, P1 (n j) (x j) := by
  rw [K_eq_mul_erase n (x + dirVec ((i, false) : Dir d)) i, add_dirVec_false_apply, if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [add_dirVec_false_apply, if_neg (Finset.ne_of_mem_erase hj)]

/-- One lazy step in coordinate `i` advances the `i`-th factor of the product
kernel by one, which is the operator identity behind `ORRW.iterate_delta0_eq`. -/
lemma K_bump (n : Fin d → ℕ) (x : Site d) (i : Fin d) :
    K (Function.update n i (n i + 1)) x
      = K n x / 2 + K n (x + dirVec (i, true)) / 4 + K n (x + dirVec (i, false)) / 4 := by
  rw [K_eq_mul_erase _ x i, K_eq_mul_erase n x i, K_shift_pos, K_shift_neg]
  simp only [Function.update_self]
  have herase : ∀ j ∈ Finset.univ.erase i,
      P1 (Function.update n i (n i + 1) j) (x j) = P1 (n j) (x j) := by
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [Finset.prod_congr rfl herase, P1_succ]
  ring

/-! ### Coordinate schedules -/

/-- How often the schedule `c` selects coordinate `i`. -/
def cnt {r : ℕ} (c : Fin r → Fin d) (i : Fin d) : ℕ := ∑ t : Fin r, if c t = i then 1 else 0

/-- The empty coordinate schedule assigns zero steps to every coordinate, anchoring the recursion by which step counts are built up along longer schedules. -/
lemma cnt_zero (c : Fin 0 → Fin d) : cnt c = fun _ => 0 := by
  funext i; simp [cnt]

/-- Extends a coordinate schedule of length r by appending a final coordinate choice, providing the inductive step for iterating the one-step decomposition of the lazy walk's kernel. -/
lemma cnt_snoc {r : ℕ} (c : Fin r → Fin d) (i : Fin d) :
    cnt (Fin.snoc c i : Fin (r + 1) → Fin d) = Function.update (cnt c) i (cnt c i + 1) := by
  funext j
  unfold cnt
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ t : Fin r,
      (if (Fin.snoc c i : Fin (r + 1) → Fin d) t.castSucc = j then 1 else 0)
        = (if c t = j then 1 else 0) := by
    intro t; rw [Fin.snoc_castSucc]
  rw [Finset.sum_congr rfl fun t _ => h1 t, Fin.snoc_last]
  by_cases hij : j = i
  · subst hij
    rw [Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne hij, if_neg (fun h => hij h.symm), add_zero]

/-- Appending one letter to a schedule. -/
def snocEquiv (r : ℕ) (d : ℕ) : ((Fin r → Fin d) × Fin d) ≃ (Fin (r + 1) → Fin d) where
  toFun p := Fin.snoc p.1 p.2
  invFun c := (fun t => c t.castSucc, c (Fin.last r))
  left_inv := by
    rintro ⟨c, i⟩
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  right_inv := by
    intro c
    exact Fin.snoc_init_self c

/-! ### The decomposition of the `r`-step kernel -/

/-- The `r`-step kernel of the lazy walk started at the origin is the average
over all `d^r` coordinate schedules of the product kernel.  This is the
formalized content of "realize a step of `Q` by choosing a coordinate uniformly
and taking a lazy step in it" (`orrw.tex`). -/
theorem iterate_delta0_eq (hd : 0 < d) (r : ℕ) (x : Site d) :
    Q^[r] (delta0 : Site d → ℝ) x = (∑ c : Fin r → Fin d, K (cnt c) x) / (d : ℝ) ^ r := by
  induction r generalizing x with
  | zero =>
    have hu : (Finset.univ : Finset (Fin 0 → Fin d)) = {fun i => i.elim0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨Finset.mem_univ _, fun c _ => ?_⟩
      funext t; exact t.elim0
    rw [Function.iterate_zero_apply, hu, Finset.sum_singleton, pow_zero, div_one,
      cnt_zero]
    unfold K delta0
    by_cases hx : x = 0
    · subst hx
      rw [if_pos rfl]
      symm
      exact Finset.prod_eq_one fun i _ => by rw [P1_zero_step]; simp
    · rw [if_neg hx]
      obtain ⟨i, hi⟩ : ∃ i : Fin d, x i ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hx (funext hc)
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [P1_zero_step, if_neg hi]
  | succ r ih =>
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hstep : ∀ y : Site d, Q^[r] (delta0 : Site d → ℝ) y
        = (∑ c : Fin r → Fin d, K (cnt c) y) / (d : ℝ) ^ r := fun y => ih y
    rw [Function.iterate_succ_apply', Q, hstep x]
    have hsum : ∀ a : Dir d, Q^[r] (delta0 : Site d → ℝ) (x + dirVec a)
        = (∑ c : Fin r → Fin d, K (cnt c) (x + dirVec a)) / (d : ℝ) ^ r :=
      fun a => hstep _
    rw [Finset.sum_congr rfl fun a _ => hsum a]
    have hdir : ∀ f : Dir d → ℝ, (∑ a : Dir d, f a)
        = ∑ i : Fin d, (f (i, true) + f (i, false)) := by
      intro f
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => by rw [Fintype.sum_bool]
    rw [hdir]
    have hL : ∑ i : Fin d, ((∑ c : Fin r → Fin d, K (cnt c) (x + dirVec ((i, true) : Dir d)))
          / (d : ℝ) ^ r
          + (∑ c : Fin r → Fin d, K (cnt c) (x + dirVec ((i, false) : Dir d))) / (d : ℝ) ^ r)
        = (∑ i : Fin d, ∑ c : Fin r → Fin d,
            (K (cnt c) (x + dirVec ((i, true) : Dir d))
              + K (cnt c) (x + dirVec ((i, false) : Dir d)))) / (d : ℝ) ^ r := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_add_distrib, ← add_div]
    rw [hL]
    have hexpand : ∀ i : Fin d,
        ∑ c : Fin r → Fin d, K (Function.update (cnt c) i (cnt c i + 1)) x
          = (∑ c : Fin r → Fin d, K (cnt c) x) / 2
            + (∑ c : Fin r → Fin d, (K (cnt c) (x + dirVec ((i, true) : Dir d))
                + K (cnt c) (x + dirVec ((i, false) : Dir d)))) / 4 := by
      intro i
      have hpt : ∀ c : Fin r → Fin d, K (Function.update (cnt c) i (cnt c i + 1)) x
          = K (cnt c) x / 2
            + (K (cnt c) (x + dirVec ((i, true) : Dir d))
              + K (cnt c) (x + dirVec ((i, false) : Dir d))) / 4 := by
        intro c; rw [K_bump]; ring
      rw [Finset.sum_congr rfl fun c _ => hpt c, Finset.sum_add_distrib, ← Finset.sum_div,
        ← Finset.sum_div]
    have hR : ∑ i : Fin d, ∑ c : Fin r → Fin d,
          K (Function.update (cnt c) i (cnt c i + 1)) x
        = (d : ℝ) * (∑ c : Fin r → Fin d, K (cnt c) x) / 2
          + (∑ i : Fin d, ∑ c : Fin r → Fin d,
              (K (cnt c) (x + dirVec ((i, true) : Dir d))
                + K (cnt c) (x + dirVec ((i, false) : Dir d)))) / 4 := by
      rw [Finset.sum_congr rfl fun i _ => hexpand i, Finset.sum_add_distrib, ← Finset.sum_div,
        ← Finset.sum_div]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hre : ∑ c' : Fin (r + 1) → Fin d, K (cnt c') x
        = ∑ i : Fin d, ∑ c : Fin r → Fin d,
            K (Function.update (cnt c) i (cnt c i + 1)) x := by
      rw [← (snocEquiv r d).sum_comp (fun c' => K (cnt c') x), Fintype.sum_prod_type,
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
      show K (cnt (Fin.snoc c i : Fin (r + 1) → Fin d)) x = _
      rw [cnt_snoc]
    rw [hre, hR]
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
    have hpne : ((d : ℝ)) ^ r ≠ 0 := pow_ne_zero _ hdne
    field_simp
    ring

end ORRW
