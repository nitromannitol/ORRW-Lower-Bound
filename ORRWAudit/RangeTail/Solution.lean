import Mathlib
import ORRW.MainTheorems
import ORRWAudit.RangeTail.SolutionBasic
import ORRWAudit.Support.RangeTailBridge

/-!
# Solution: RangeTail

The challenge module `ORRWAudit/RangeTail/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`.  This solution imports the
repository together with `ORRWAudit.RangeTail.SolutionBasic`, a verbatim copy of the
challenge's vocabulary, and proves the byte-identical statement from
`ORRW.range_tail`.  Every vocabulary constant in this statement is definitionally
equal to its repository counterpart (`ORRWAudit/Support/RangeTailBridge.lean` records each
identification), so the library theorem closes the goal by `exact`.
-/

namespace ORRWAudit

open MeasureTheory Filter

/-- Theorem 1.2 (`thm:whp`), the stretched-exponential lower tail. -/
theorem range_tail (d : ℕ) (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, C * β ≤ (n : ℝ) →
      prb (d := d) n β (fun w =>
          ((R w n).card : ℝ)
            < c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)))
        ≤ Real.exp (-(c * ((n : ℝ) / β) ^ (((d : ℝ) - 1) / ((d : ℝ) + 1)))) := by
  exact _root_.ORRW.range_tail d hd

end ORRWAudit
