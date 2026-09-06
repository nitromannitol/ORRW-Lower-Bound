/-
Frozen statement of the exit time bounds of Bou-Rabee--Peres, *Once-reinforced
random walk on `ℤ^d` has range exponent at least `d/(d+1)`*, Section 2,
Lemma (Exit time bounds), label `lem:max-exit`, `orrw.tex:464-473`:

  "Let `d ≥ 1`. Every finite nonempty `A ⊂ ℤ^d` satisfies
     `max_{x ∈ A} u_A(x) ≤ C|A|^{2/d}`,
     `max_{x ∉ A} h_A(x) ≤ C|A|^{2/d}`,
     `T(A) ≤ C|A|^{1+2/d}`."

Modelling decisions.

* Ruling F-101 (order of quantifiers).  The paper's `C` depends only on `d`, so
  it is bound before `A`.  A `C` chosen after `A` would make the statement
  trivially true.

* Ruling F-102 (maxima as universal bounds).  `max_{x ∈ A}` and `max_{x ∉ A}`
  are rendered as bounds holding at every such `x`.  This is equivalent, and
  for `max_{x ∉ A}` it avoids having to assert that the supremum over the
  infinite set `A^c` is attained.

* Ruling F-103 (`0 < C`).  Positivity of `C` is asserted.  It strengthens the
  statement and rules out a degenerate negative constant.

* Ruling F-104 (real exponents).  `|A|^{2/d}` and `|A|^{1+2/d}` are `Real.rpow`
  powers of the cardinality cast to `ℝ`.
-/
import ORRW.Lattice
import ORRW.Support.ExitTime

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.max_exit {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Finset (Site d), A.Nonempty →
      (∀ x ∈ A, u A x ≤ C * (A.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ∧
      (∀ x ∉ A, h A x ≤ C * (A.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ∧
      T A ≤ C * (A.card : ℝ) ^ (1 + (2 : ℝ) / (d : ℝ))
-- FROZEN-STATEMENT-END
:= ORRW.Support.exit_time_bounds hd
