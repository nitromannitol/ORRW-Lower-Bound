import Mathlib
import Audit.Support.Vocabulary

/-!
# The audited statements in the challenge environment

Each audited statement, elaborated as a proposition in exactly the environment
of the challenges: this module imports only Mathlib and the vocabulary.
`Audit/StatementRegression.lean` checks that each solution theorem has
exactly this type, so that no repository name or instance leaks into a
solution statement.
-/

namespace ORRWAudit.Statements

open ORRWAudit
open MeasureTheory Filter

-- The hypothesis names are kept so that the text matches the challenges.
set_option linter.unusedVariables false

/-- The statement of `Audit/RangeLowerBound/Challenge.lean`. -/
def range_lower_bound : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d),
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ,
      c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))
        ≤ expect (d := d) n β (fun w => ((R w n).card : ℝ))

/-- The statement of `Audit/RangeTail/Challenge.lean`. -/
def range_tail : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d),
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, C * β ≤ (n : ℝ) →
      prb (d := d) n β (fun w =>
          ((R w n).card : ℝ)
            < c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)))
        ≤ Real.exp (-(c * ((n : ℝ) / β) ^ (((d : ℝ) - 1) / ((d : ℝ) + 1))))

/-- The statement of `Audit/RangeAlmostSure/Challenge.lean`. -/
def range_ae : Prop :=
  ∀ {d : ℕ} [hd0 : Fact (0 < d)] (hd : 2 ≤ d),
    ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 1 ≤ β),
      ∀ᵐ ω ∂(@pathMeasure d hd0 β ⟨hβ⟩), ∀ᶠ n : ℕ in atTop,
        c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))
          ≤ ((R (ofPath n ω) n).card : ℝ)

/-- The statement of `Audit/OccupationMeasure/Challenge.lean`. -/
def occupation_measure : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d),
    ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, 1 ≤ n → ∀ N : ℕ, n ≤ N → ∀ z : Site d,
      ∑ j ∈ Finset.range n, prb (d := d) N β (fun w => pos w j = z)
        ≤ C * β * (n : ℝ) ^ (1 / ((d : ℝ) + 1))

end ORRWAudit.Statements
