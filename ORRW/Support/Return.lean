/-
Support lemmas for Section 8 of `orrw.tex` (`sec:return`).

`one_le_return_sum` is an anti-vacuity guard for `thm-return`: the `j = 0` term
of that theorem's left-hand side is identically `1`, because the walk starts at
the origin and `prob` is a probability mass function.  So the left-hand side is
always at least `1`, and the theorem genuinely constrains its constant rather
than being satisfied by a degenerate measure.
-/
import ORRW.Basic
import ORRW.Support.Guards

namespace ORRW

open Finset

/-- Every direction word has strictly positive probability, since each step
weight and each total weight is positive. -/
theorem prob_pos {d n : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) (w : Fin n → Dir d) :
    0 < prob β w :=
  Finset.prod_pos fun k _ =>
    div_pos (stepWeight_pos hβ w (k : ℕ) (w k)) (totalWeight_pos hd hβ w (k : ℕ))

end ORRW
