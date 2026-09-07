/-
Frozen statement of Proposition 7.1 of Bou-Rabee--Peres, *Once-reinforced random
walk on `ℤ^d` has range exponent at least `d/(d+1)`*, Section 7, Proposition
(The exponents are optimal), label `prop:beta-sharp`, `orrw.tex:912-922`:

  "Let `d ≥ 2`.  For every `β ≥ 1` and every integer `n ≥ 1`,
     `E_β|R_n| ≤ 2 + 2dn/β`.                                (`eq:range-upper`)
   Consequently, if the real numbers `γ` and `c > 0` satisfy
   `E_β|R_n| ≥ cβ^{-γ}n^{d/(d+1)}` for all `β ≥ 1` and all `n ≥ 1`, then
   `γ ≥ d/(d+1)`.  If the real numbers `s` and `c > 0` satisfy
   `E_β|R_n| ≥ cβ^{-d/(d+1)}n^{s}` for all `β ≥ 1` and all `n ≥ 1`, then
   `s ≤ d/(d+1)`."

Modelling decisions.

* Ruling F-631 (all three assertions are frozen together).  The two optimality
  clauses are stated in the paper as consequences of `eq:range-upper` and are
  frozen with it as one declaration, so that the constant-free content of the
  proposition is not split across nodes.

* Ruling F-632 (the hypotheses of the two clauses are the paper's).  Each clause
  hypothesizes the lower bound of `eq:main-range` with the exponent under test,
  quantified over all `β ≥ 1` and all integers `n ≥ 1`, exactly as in
  `ORRW.Frozen.range_lower_bound`, and concludes a numerical inequality on that
  exponent.  Neither hypothesis forces its conclusion: each is satisfiable, by
  `thm:main`, at the true exponents `γ = d/(d+1)` and `s = d/(d+1)`.

* Ruling F-633 (real powers).  `β^{-γ}`, `β^{-d/(d+1)}`, `n^{d/(d+1)}` and `n^s`
  are `Real.rpow` powers, as in `ORRW/Frozen/RangeLowerBound.lean`; the bases
  are positive on the stated ranges.

* Ruling F-634 (the expectation).  `E_β|R_n|` is
  `ORRW.expect n β (fun w => ((ORRW.R w n).card : ℝ))`, the same term as in
  `ORRW.Frozen.range_lower_bound`, so the three clauses can be composed with it
  without a translation lemma.
-/
import ORRW.Lattice
import ORRW.Support.RangeUpper

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.exponents_optimal (d : ℕ) (hd : 2 ≤ d) :
    (∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, 1 ≤ n →
        ORRW.expect (d := d) n β (fun w => ((ORRW.R w n).card : ℝ))
          ≤ 2 + 2 * (d : ℝ) * (n : ℝ) / β) ∧
      (∀ γ c : ℝ, 0 < c →
        (∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, 1 ≤ n →
            c * β ^ (-γ) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))
              ≤ ORRW.expect (d := d) n β (fun w => ((ORRW.R w n).card : ℝ))) →
        (d : ℝ) / ((d : ℝ) + 1) ≤ γ) ∧
      (∀ s c : ℝ, 0 < c →
        (∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, 1 ≤ n →
            c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ s
              ≤ ORRW.expect (d := d) n β (fun w => ((ORRW.R w n).card : ℝ))) →
        s ≤ (d : ℝ) / ((d : ℝ) + 1))
-- FROZEN-STATEMENT-END
:= by
  have hd0 : 0 < d := by omega
  refine ⟨fun β hβ n hn => ORRW.expect_card_range_le (d := d) hd0 hβ hn, ?_, ?_⟩
  · intro γ c hc hyp
    have key : ∀ n : ℕ, 1 ≤ n →
        c * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1) - γ) ≤ 2 + 2 * (d : ℝ) := by
      intro n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
      have h1 := hyp (n : ℝ) hn1 n hn
      have h2 := ORRW.expect_card_range_le (d := d) hd0 hn1 hn
      have h3 : 2 * (d : ℝ) * (n : ℝ) / (n : ℝ) = 2 * (d : ℝ) := by
        field_simp
      rw [h3] at h2
      have h4 : (n : ℝ) ^ (-γ) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))
          = (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1) - γ) := by
        rw [← Real.rpow_add hn0]; congr 1; ring
      calc c * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1) - γ)
          = c * (n : ℝ) ^ (-γ) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) := by rw [← h4]; ring
        _ ≤ ORRW.expect (d := d) n (n : ℝ) (fun w => ((ORRW.R w n).card : ℝ)) := h1
        _ ≤ 2 + 2 * (d : ℝ) := h2
    linarith [ORRW.rpow_exponent_nonpos hc key]
  · intro s c hc hyp
    have key : ∀ n : ℕ, 1 ≤ n →
        c * (n : ℝ) ^ (s - (d : ℝ) / ((d : ℝ) + 1)) ≤ 2 + 2 * (d : ℝ) := by
      intro n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
      have h1 := hyp (n : ℝ) hn1 n hn
      have h2 := ORRW.expect_card_range_le (d := d) hd0 hn1 hn
      have h3 : 2 * (d : ℝ) * (n : ℝ) / (n : ℝ) = 2 * (d : ℝ) := by
        field_simp
      rw [h3] at h2
      have h4 : (n : ℝ) ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ s
          = (n : ℝ) ^ (s - (d : ℝ) / ((d : ℝ) + 1)) := by
        rw [← Real.rpow_add hn0]; congr 1; ring
      calc c * (n : ℝ) ^ (s - (d : ℝ) / ((d : ℝ) + 1))
          = c * (n : ℝ) ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ s := by rw [← h4]; ring
        _ ≤ ORRW.expect (d := d) n (n : ℝ) (fun w => ((ORRW.R w n).card : ℝ)) := h1
        _ ≤ 2 + 2 * (d : ℝ) := h2
    linarith [ORRW.rpow_exponent_nonpos hc key]
