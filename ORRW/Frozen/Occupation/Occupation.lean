/-
Frozen statement of Theorem 8.2 of Bou-Rabee--Peres, *Once-reinforced random
walk on `ℤ^d` has range exponent at least `d/(d+1)`*, Section 8, Theorem
(Occupation of a site), label `thm:return`, display `eq:occupation`,
`orrw.tex:1227-1247`:

  "Let `d ≥ 2`.  There is a constant `C < ∞`, depending only on `d`, such that
   for every `β ≥ 1`, every site `z`, every integer `m ≥ 0` and every integer
   `h ≥ 1`,
     `E_β ∑_{j=m}^{m+h-1} 1_{{X_j = z}} ≤ C[log(h+2) + (β-1)^{2/3} h^{1/3}]`,
       `d = 2`,
     `E_β ∑_{j=m}^{m+h-1} 1_{{X_j = z}} ≤ C[1 + (β-1)^{d/(d+1)} h^{1/(d+1)}]`,
       `d ≥ 3`."

Modelling decisions.

* Ruling F-811 (the expectation is a sum of probabilities at one horizon).
  Under ruling R-001 there is no measure on infinite paths: `ORRW.prb N β` is a
  mass function on the finite set of direction words of one fixed length `N`.
  The expectation of the occupation count is expanded by linearity into
  `∑_{j ∈ [m, m+h)} P_β{X_j = z}`, and every one of those probabilities is
  evaluated at a single horizon `N`.  Stating the `j`-th term at horizon `j`
  instead would need a consistency lemma between horizons; a common horizon
  needs none, since `ORRW.pos w j` is defined for every `j`.

* Ruling F-812 (the horizon is universally quantified above `m + h`).  `N` is
  quantified over every horizon with `m + h ≤ N`, which is stronger than fixing
  one and is the convention of ruling F-612.  The hypothesis `m + h ≤ N` is load
  bearing: past its length a direction word freezes the walk
  (`ORRW.pos_of_length_le`), so at a horizon below `m + h` the indices
  `j ≥ N` would all report the same site and the left-hand side would be a
  statement about a degenerate walk rather than about `X_m, …, X_{m+h-1}`.

* Ruling F-813 (`C` is bound before `β`, `z`, `m`, `h` and `N`).  The paper says
  "depending only on `d`", so `C` is bound existentially right after `d`.

* Ruling F-814 (the two cases are merged).  The two displayed bounds differ only
  in their first summand, since at `d = 2` the exponents `2/3` and `1/3` are
  `d/(d+1)` and `1/(d+1)`.  `if d = 2 then Real.log (h+2) else 1` reproduces the
  paper's display in both cases, and `2 ≤ d` makes them exhaustive.

* Ruling F-815 (real exponents, and `β - 1` may be zero).  `(β-1)^{d/(d+1)}` and
  `h^{1/(d+1)}` are `Real.rpow` powers.  At `β = 1` the base is `0` and the
  exponent is nonzero, so `Real.rpow` gives `0`, which is the paper's reading:
  the reinforcement term is absent for simple random walk.

* Ruling F-816 (the simpler bound is not part of this node).  The paper adds
  "and in either case the right-hand side is at most `C β h^{1/(d+1)}`"
  (`orrw.tex`).  That is a consequence of the display, used only to
  derive `eq:cesaro`, and it is `ORRW.Frozen.occupation_cesaro` that records the
  form the rest of the paper uses.  This node freezes the two-case display.

Vacuity.  The bound is not trivially true.  Each summand is a probability, so
the left-hand side is at most `h`; for `d ≥ 3` and `β = 1` the right-hand side
is the constant `C`, and for `d = 2` and `β = 1` it is `C log(h+2)`, both far
below `h`.  Nor can the left-hand side collapse to `0`: at `z = 0` and `m = 0`
the term `j = 0` is `ORRW.prb N β (fun w => ORRW.pos w 0 = 0)`, whose event is
all of the sample space, so it equals `1` by `ORRW.Frozen.sum_prob_eq_one`; the
bound therefore forces `C` to be positive.  Non-degenerate instance: `d = 2`,
`β = 3`, `z = 0`, `m = 0`, `h = 5`, `N = 5`, where the right-hand side is
`C(log 7 + 2^{2/3} · 5^{1/3}) ≈ 4.66 C` and the left-hand side lies in `[1, 5]`.
-/
import ORRW.Basic
import ORRW.Support.Occupation
import ORRW.Support.Optimize

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.occupation (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β → ∀ z : ORRW.Site d, ∀ m h : ℕ, 1 ≤ h →
      ∀ N : ℕ, m + h ≤ N →
        ∑ j ∈ Finset.Ico m (m + h), ORRW.prb (d := d) N β (fun w => ORRW.pos w j = z)
          ≤ C * ((if d = 2 then Real.log ((h : ℝ) + 2) else 1)
              + (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1))
                * (h : ℝ) ^ (1 / ((d : ℝ) + 1)))
-- FROZEN-STATEMENT-END
:= by
  have hd0 : 0 < d := by omega
  obtain ⟨C, hC⟩ := ORRW.optimize_R d hd (ORRW.occConst d) (ORRW.occConst_nonneg d)
  refine ⟨C, fun β hβ z m h hh N hN => ?_⟩
  exact hC (β - 1) (by linarith) h hh _
    (ORRW.occupation_trivial hd0 hβ z m h)
    (fun R hR => ORRW.occupation_bound_R hd hβ z m h hh hN hR)
