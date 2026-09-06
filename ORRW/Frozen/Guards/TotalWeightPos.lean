/-
Guard: the denominator of the step rule never vanishes.

`stepProb` divides by `totalWeight`.  If that could be zero then `prob`
would be zero and every expectation bound in the development would hold
vacuously.  The `0 < d` hypothesis is what excludes the empty direction set.
-/
import ORRW.Basic
import ORRW.Support.Guards

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.totalWeight_pos {d n : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β)
    (w : Fin n → ORRW.Dir d) (k : ℕ) : 0 < ORRW.totalWeight β w k
-- FROZEN-STATEMENT-END
:= _root_.ORRW.totalWeight_pos hd hβ w k
