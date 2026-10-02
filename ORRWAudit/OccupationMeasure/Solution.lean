import Mathlib
import ORRW.MainTheorems
import ORRWAudit.OccupationMeasure.SolutionBasic
import ORRWAudit.Support.OccupationMeasureBridge

/-!
# Solution: OccupationMeasure

The challenge module `ORRWAudit/OccupationMeasure/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`.  This solution imports the
repository together with `ORRWAudit.OccupationMeasure.SolutionBasic`, a verbatim copy of the
challenge's vocabulary, and proves the byte-identical statement from
`ORRW.occupation_measure`.  Every vocabulary constant in this statement is definitionally
equal to its repository counterpart (`ORRWAudit/Support/OccupationMeasureBridge.lean` records each
identification), so the library theorem closes the goal by `exact`.
-/

namespace ORRWAudit

open MeasureTheory Filter

/-- Theorem 1.3 (`thm:occupation-intro`), the occupation measure bound. -/
theorem occupation_measure (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, 1 ≤ n → ∀ N : ℕ, n ≤ N → ∀ z : Site d,
      ∑ j ∈ Finset.range n, prb (d := d) N β (fun w => pos w j = z)
        ≤ C * β * (n : ℝ) ^ (1 / ((d : ℝ) + 1)) := by
  exact _root_.ORRW.occupation_measure d hd

end ORRWAudit
