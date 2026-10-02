import Mathlib
import ORRW.MainTheorems
import ORRWAudit.RangeAlmostSure.SolutionBasic
import ORRWAudit.Support.RangeAlmostSureBridge

/-!
# Solution: RangeAlmostSure

The challenge module `ORRWAudit/RangeAlmostSure/Challenge.lean` imports only Mathlib and
states the theorem with one intentional `sorry`.  This solution imports the
repository together with `ORRWAudit.RangeAlmostSure.SolutionBasic`, a verbatim copy of the
challenge's vocabulary, and proves the byte-identical statement from
`ORRW.range_ae`.  Every vocabulary constant in this statement is definitionally
equal to its repository counterpart (`ORRWAudit/Support/RangeAlmostSureBridge.lean` records each
identification), so the library theorem closes the goal by `exact`.
-/

namespace ORRWAudit

open MeasureTheory Filter

/-- The almost-sure range lower bound stated after Theorem 1.2 (`thm:whp`). -/
theorem range_ae {d : ℕ} [hd0 : Fact (0 < d)] (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 1 ≤ β),
      ∀ᵐ ω ∂(@pathMeasure d hd0 β ⟨hβ⟩), ∀ᶠ n : ℕ in atTop,
        c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))
          ≤ ((R (ofPath n ω) n).card : ℝ) := by
  exact _root_.ORRW.range_ae hd

end ORRWAudit
