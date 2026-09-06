/-
Frozen statement of Proposition 5.2 of Bou-Rabee--Peres, *Once-reinforced random
walk on `ℤ^d` has range exponent at least `d/(d+1)`*, Section 5, Proposition
(Tail of `σ_k`), label `prop:tail`, `orrw.tex:933-941`:

  "Let `d ≥ 2` and let `K` be the constant of Proposition `prop:charge`.  There
   is `c > 0`, depending only on `d`, such that for every `β ≥ 1` and every
   integer `k ≥ 1`,
     `P_β{σ_k > 8Kβk^{1+1/d}} ≤ exp(-ck^{(d-1)/d})`."

Modelling decisions.

* Ruling F-611 (`K` is existentially bound here too).  The paper names `K` as
  "the constant of `prop:charge`", and `ORRW.Frozen.accumulated_charge` binds
  that constant existentially (ruling F-522).  There is therefore no term to
  refer to, and `K` is bound existentially here as well, before `β` and `k`, so
  that it depends only on `d`.  This is the same assertion: the pair `(c, K)`
  produced here is a pair of constants depending only on `d` for which the
  displayed tail bound holds, and any constant valid in `prop:charge` is valid
  here.

* Ruling F-612 (the event is measured at a horizon past the threshold).  Under
  ruling R-001 a probability is a mass on words of one fixed length `N`, and
  `ORRW.sigma` is evaluated on such a word.  The event `{σ_k > 8Kβk^{1+1/d}}` is
  therefore measured at every horizon `N` at least the threshold
  `8Kβk^{1+1/d}`; at such a horizon the event is decided by the word, since
  `ORRW.sigma_le_iff` (the paper's `eq:sigma-range`) determines `{σ_k ≤ m}` for
  every `m ≤ N`, and the paper's `σ_k = ∞` is recorded as `N + 1`, which exceeds
  the threshold, as it should (ruling P-004).  Quantifying over all such `N` is
  stronger than fixing one and needs no consistency lemma between horizons.

* Ruling F-613 (`0 < c`, `0 < K`).  Positivity of both constants is asserted.

* Ruling F-614 (real exponents).  `k^{1+1/d}` and `k^{(d-1)/d}` are `Real.rpow`
  powers; `(d-1)/d` is formed in `ℝ`, not by truncated subtraction in `ℕ`.
-/
import ORRW.Potential
import ORRW.Support.SigmaTail

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.sigma_tail (d : ℕ) (hd : 2 ≤ d) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ β : ℝ, 1 ≤ β → ∀ k : ℕ, 1 ≤ k → ∀ N : ℕ,
      8 * K * β * (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) ≤ (N : ℝ) →
      prb (d := d) N β
          (fun w => 8 * K * β * (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) < (sigma w k : ℝ))
        ≤ Real.exp (-(c * (k : ℝ) ^ (((d : ℝ) - 1) / (d : ℝ))))
-- FROZEN-STATEMENT-END
:= ORRW.Support.sigma_tail_of hd
