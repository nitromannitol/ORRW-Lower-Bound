import ORRW.Frozen.RangeLowerBound
import ORRW.Frozen.RangeTail
import ORRW.Frozen.AlmostSure.RangeAlmostSure
import ORRW.Frozen.Occupation.OccupationMeasure

/-!
# Main results

The main theorems of the formalization of *Once-reinforced random walk on `ℤ^d`
has range exponent at least `d/(d+1)`* (Ahmed Bou-Rabee and Yuval Peres),
stated here in full: Theorem 1.1 (`thm:main`), the range lower bound;
Theorem 1.2 (`thm:whp`), its stretched-exponential lower tail; the almost-sure
bound the paper draws from Theorem 1.2 by the Borel–Cantelli lemma; and
Theorem 1.3 (`thm:occupation-intro`), the bound on the occupation measure.

Each theorem below restates its certified counterpart in `ORRW/Frozen/` and is
proved by `exact` of it, so the statements displayed in this file are the
certified ones.  Nothing is assumed: no theorem takes a cited result as a
hypothesis.

The model is that of `ORRW/Basic.lean`.  A direction word `w : Fin n → Dir d`
lists the first `n` steps of the walk, `ORRW.prob β w` is its probability under
once-reinforced random walk with parameter `β`, and `ORRW.expect` and
`ORRW.prb` are expectation and probability under that law.  `ORRW.R w n` is
the range `R_n = {X_0, …, X_n}` and `ORRW.pos w j` the position `X_j`.  The
almost-sure statement is about the law `ORRW.pathMeasure β` of the walk on
infinite direction words, built from the one-step kernels by the
Ionescu-Tulcea theorem in `ORRW/Support/InfinitePath.lean`, and
`ORRW.ofPath n ω` is the word of the first `n` letters of `ω`.

* `ORRW.range_lower_bound`: Theorem 1.1.  For `d ≥ 2` there is `c > 0` with
  `E_β |R_n| ≥ c β^{-d/(d+1)} n^{d/(d+1)}` for every `β ≥ 1` and every `n`.
* `ORRW.range_tail`: Theorem 1.2.  For `d ≥ 2` there are `c, C > 0` with
  `P_β(|R_n| < c β^{-d/(d+1)} n^{d/(d+1)}) ≤ exp(-c (n/β)^{(d-1)/(d+1)})`
  for every `β ≥ 1` and every `n ≥ C β`.
* `ORRW.range_ae`: the almost-sure bound after Theorem 1.2.  For `d ≥ 2` there
  is `c > 0` such that for every `β ≥ 1`, almost surely,
  `|R_n| ≥ c β^{-d/(d+1)} n^{d/(d+1)}` for all large `n`, which implies the
  printed bound on the lower limit.
* `ORRW.occupation_measure`: Theorem 1.3.  For `d ≥ 2` there is `C` with
  `∑_{j<n} P_β(X_j = z) ≤ C β n^{1/(d+1)}` for every `β ≥ 1`, every `n ≥ 1`
  and every site `z`; the left side is `E_β L_n(z)`, read in the law of any
  horizon `N ≥ n`.

All four reduce to the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); see `ORRW/Meta/AxiomsAudit.lean`.
-/

open MeasureTheory Filter

/-- **Theorem 1.1** (`thm:main`), the range lower bound.  The certified
statement is `ORRW.Frozen.range_lower_bound`, restated unchanged. -/
theorem ORRW.range_lower_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ,
      c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))
        ≤ ORRW.expect (d := d) n β (fun w => ((ORRW.R w n).card : ℝ)) := by
  exact ORRW.Frozen.range_lower_bound d hd

/-- **Theorem 1.2** (`thm:whp`), the stretched-exponential lower tail.  The
certified statement is `ORRW.Frozen.range_tail`, restated unchanged. -/
theorem ORRW.range_tail (d : ℕ) (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, C * β ≤ (n : ℝ) →
      ORRW.prb (d := d) n β (fun w =>
          ((ORRW.R w n).card : ℝ)
            < c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)))
        ≤ Real.exp (-(c * ((n : ℝ) / β) ^ (((d : ℝ) - 1) / ((d : ℝ) + 1)))) := by
  exact ORRW.Frozen.range_tail d hd

/-- The almost-sure range lower bound stated after **Theorem 1.2**
(`thm:whp`).  The certified statement is `ORRW.Frozen.range_ae`, restated
unchanged. -/
theorem ORRW.range_ae {d : ℕ} [hd0 : Fact (0 < d)] (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 1 ≤ β),
      ∀ᵐ ω ∂(@ORRW.pathMeasure d hd0 β ⟨hβ⟩), ∀ᶠ n : ℕ in atTop,
        c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))
          ≤ ((ORRW.R (ORRW.ofPath n ω) n).card : ℝ) := by
  exact ORRW.Frozen.range_ae hd

/-- **Theorem 1.3** (`thm:occupation-intro`), the occupation measure bound.
The certified statement is `ORRW.Frozen.occupation_measure`, restated
unchanged. -/
theorem ORRW.occupation_measure (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, 1 ≤ n → ∀ N : ℕ, n ≤ N → ∀ z : ORRW.Site d,
      ∑ j ∈ Finset.range n, ORRW.prb (d := d) N β (fun w => ORRW.pos w j = z)
        ≤ C * β * (n : ℝ) ^ (1 / ((d : ℝ) + 1)) := by
  exact ORRW.Frozen.occupation_measure d hd
