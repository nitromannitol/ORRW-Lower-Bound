/-
Guard: the law of the first `n` steps has total mass one.

This is the positive form of the vacuity guard: it certifies that `prob` is a
probability mass function on direction words, so that `expect` and `prb` mean
what their names say and the two frozen theorems are not statements about a
defective measure.
-/
import ORRW.Basic
import ORRW.Support.Guards

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.sum_prob_eq_one {d n : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) :
    ∑ w : Fin n → ORRW.Dir d, ORRW.prob β w = 1
-- FROZEN-STATEMENT-END
:= _root_.ORRW.sum_prob_eq_one hd hβ n
