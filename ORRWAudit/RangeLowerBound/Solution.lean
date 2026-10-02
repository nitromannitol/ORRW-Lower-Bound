import Mathlib
import ORRW.MainTheorems
import ORRWAudit.RangeLowerBound.SolutionBasic
import ORRWAudit.Support.RangeLowerBoundBridge

/-!
# Solution: RangeLowerBound

The challenge module `ORRWAudit/RangeLowerBound/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`.  This solution imports the
repository together with `ORRWAudit.RangeLowerBound.SolutionBasic`, a verbatim copy of the
challenge's vocabulary, and proves the byte-identical statement from
`ORRW.range_lower_bound`.  Every vocabulary constant in this statement is definitionally
equal to its repository counterpart (`ORRWAudit/Support/RangeLowerBoundBridge.lean` records each
identification), so the library theorem closes the goal by `exact`.
-/

namespace ORRWAudit

open MeasureTheory Filter

/-- Theorem 1.1 (`thm:main`), the range lower bound. -/
theorem range_lower_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ,
      c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))
        ≤ expect (d := d) n β (fun w => ((R w n).card : ℝ)) := by
  exact _root_.ORRW.range_lower_bound d hd

end ORRWAudit
