/-
Frozen statement of Proposition 3.3 of Bou-Rabee--Peres, *Once-reinforced random
walk on `ℤ^d` has range exponent at least `d/(d+1)`*, Section 3, Proposition
(Bound on the nondecreasing process), label `prop:charge`, `orrw.tex:669-676`:

  "Let `d ≥ 2`.  There is a constant `K < ∞`, depending only on `d`, such that
   for every `β ≥ 1`, almost surely,
     `Γ_n ≤ Kβ|E_n|^{1+1/d}`  for every integer `n ≥ 0`."   (`eq:charge-bound`)

Modelling decisions.

* Ruling F-521 ("almost surely" is "for every word").  Under ruling R-001 the
  sample space at horizon `n` is the finite set `Fin n → Dir d`, and every word
  has positive probability, since every step weight is positive
  (`ORRW.stepWeight_pos`).  An almost sure inequality between functions of the
  word is therefore an inequality holding at every word, and the statement below
  is deterministic.

* Ruling F-522 (order of quantifiers).  `K` depends only on `d`, so it is bound
  before `β`, before the horizon, before the word and before the time.

* Ruling F-523 (time and horizon are separate).  The paper's `n` is a time; in
  the model it is also the length of the word.  The bound is stated for every
  word length `n`, every word `w : Fin n → Dir d` and every time `m : ℕ`,
  including `m > n`.  Nothing is thereby assumed away: past the horizon the
  traversed-edge set is constant, since `ORRW.E` is cut off at `min k n`, so
  `η` vanishes and both sides are constant in `m` beyond `n`.

* Ruling F-524 (`0 < K`).  Positivity of `K` is asserted, as in
  `ExitTimeBounds.lean` (ruling F-103); it strengthens the statement and rules
  out a degenerate negative constant.

* Ruling F-525 (real exponent).  `|E_m|^{1+1/d}` is a `Real.rpow` power of the
  cardinality cast to `ℝ`.
-/
import ORRW.Potential
import ORRW.Support.ChargeAssembly

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.accumulated_charge {d : ℕ} (hd : 2 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, ∀ w : Fin n → Dir d, ∀ m : ℕ,
      Gamma β w m ≤ K * β * ((E w m).card : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ))
-- FROZEN-STATEMENT-END
:= ORRW.Support.accumulated_charge_of hd
