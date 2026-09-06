/-
Numeric witness: an explicit value the normalization can be checked against.

With `d = 2` and one step the walk has crossed no edge, so all four incident
weights equal one, each direction has probability `1/4`, and the range is the
origin together with the site reached.  Hence the expected range after one step
is exactly `2`, for every `β ≥ 1`.  A model whose constants were wrong by a
factor would fail here.
-/
import ORRW.Basic
import ORRW.Support.Guards

open ORRW Finset

-- `hβ` is not needed: at time zero no edge is traversed, so the step rule does
-- not see `β` at all.  The frozen statement is the `β ≥ 1` specialization of
-- `ORRW.expect_card_range_one_step`, which holds for every real `β`.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.expect_card_range_one_step (β : ℝ) (hβ : 1 ≤ β) :
    ORRW.expect (d := 2) 1 β (fun w => ((ORRW.R w 1).card : ℝ)) = 2
-- FROZEN-STATEMENT-END
:= _root_.ORRW.expect_card_range_one_step β
