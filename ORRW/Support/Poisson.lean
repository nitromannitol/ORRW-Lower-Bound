/-
The Poisson equation for the truncated Green function, `orrw.tex`
(`eq:poisson`):

  "Since `Q - I = ½(P - I)`, the sum telescopes:
     `(P - I)(-g_R) = 2(1_{{0}} - Q^R(0,·))`."

`P` is the simple-random-walk operator, so `(P - I)f(x)` is
`(2d)^{-1} ∑_a f(x + e_a) - f(x)`; the form recorded below is that display
multiplied by `2d`, which is how it enters the compensator identity.
-/
import Mathlib
import ORRW.LazyWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

variable {d : ℕ}

/-- `Q` is linear over a `Finset` sum. -/
theorem Q_sum {ι : Type*} (s : Finset ι) (f : ι → Site d → ℝ) (x : Site d) :
    Q (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, Q (f i) x := by
  unfold Q
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm]

/-- `Q g_R - g_R = Q^R(0,·) - 1_{{0}}`: the telescoping of `orrw.tex`. -/
theorem Q_gR_sub (R : ℕ) (x : Site d) :
    Q (gR R) x - gR R x = Q^[R] (delta0 : Site d → ℝ) x - delta0 x := by
  have hQ : Q (gR R) x = ∑ r ∈ Finset.range R, Q^[r + 1] (delta0 : Site d → ℝ) x := by
    have : (gR R : Site d → ℝ)
        = fun y => ∑ r ∈ Finset.range R, Q^[r] (delta0 : Site d → ℝ) y := rfl
    rw [this, Q_sum]
    exact Finset.sum_congr rfl fun r _ =>
      (congrFun (Function.iterate_succ_apply' Q r (delta0 : Site d → ℝ)) x).symm
  have hg : gR R x = ∑ r ∈ Finset.range R, Q^[r] (delta0 : Site d → ℝ) x := rfl
  rw [hQ, hg, ← Finset.sum_sub_distrib]
  exact Finset.sum_range_sub (fun r => Q^[r] (delta0 : Site d → ℝ) x) R

/-- `∑_a (g_R(x + e_a) - g_R(x)) = 4d (Q^R(0,x) - 1_{{x = 0}})`, which is
`eq:poisson` multiplied by `2d`. -/
theorem sum_dir_gR_diff (hd : 0 < d) (R : ℕ) (x : Site d) :
    ∑ a : Dir d, (gR R (x + dirVec a) - gR R x)
      = 4 * (d : ℝ) * (Q^[R] (delta0 : Site d → ℝ) x - delta0 x) := by
  have hdR : (0 : ℝ) < 4 * (d : ℝ) := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hcard : ((Finset.univ : Finset (Dir d)).card : ℝ) = 2 * (d : ℝ) := by
    simp [Fintype.card_prod]
    ring
  have hQdef : Q (gR R) x = gR R x / 2 + (∑ a : Dir d, gR R (x + dirVec a)) / (4 * (d : ℝ)) := rfl
  have hsum : ∑ a : Dir d, gR R (x + dirVec a) = 4 * (d : ℝ) * (Q (gR R) x - gR R x / 2) := by
    rw [hQdef]
    field_simp
    ring
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, nsmul_eq_mul, hcard, ← Q_gR_sub]
  ring

end ORRW
