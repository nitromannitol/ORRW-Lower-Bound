/-
Frozen statement of the insertion inequality of Bou-Rabee--Peres,
*Once-reinforced random walk on `ℤ^d` has range exponent at least `d/(d+1)`*,
Section 2, Lemma (Sum over successive vertex additions), label `lem:insertion`,
`orrw.tex:573-581`:

  "Let `d ≥ 2`, let `M ≥ 1` be an integer, let `x_1, …, x_M` be distinct
   vertices of `ℤ^d`, and let `A_i := {x_1, …, x_i}` for `0 ≤ i ≤ M`.  Then
     `∑_{i=1}^M (h_{A_{i-1}}(x_i) + u_{A_i}(x_i)) ≤ CM^{1+1/d}`."

Modelling decisions.

* Ruling F-401 (the insertion order).  As in `ResistancePacking.lean`
  (ruling F-301), `x_1, …, x_M` is an injective `x : Fin M → Site d`.  For the
  `0`-indexed step `i : Fin M` the paper's `A_{i-1}` is `(Finset.Iio i).image x`
  and the paper's `A_i` is `insert (x i) ((Finset.Iio i).image x)`.  In
  particular `A_0 = ∅` is the empty image at `i = 0`.

* Ruling F-402 (order of quantifiers).  `C` depends only on `d`, so it is bound
  before `M` and before `x`.

* Ruling F-403 (`0 < C`).  Positivity of `C` is asserted.

* Ruling F-404 (real exponent).  `M^{1+1/d}` is a `Real.rpow` power.
-/
import ORRW.Lattice
import ORRW.Support.InsertionSum
import ORRW.Frozen.Insertion.ExitTimeBounds
import ORRW.Frozen.Insertion.ResistancePacking

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.insertion_inequality {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → ∀ x : Fin M → Site d, Function.Injective x →
      ∑ i : Fin M,
          (h ((Finset.Iio i).image x) (x i)
            + u (insert (x i) ((Finset.Iio i).image x)) (x i))
        ≤ C * (M : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ))
-- FROZEN-STATEMENT-END
:= by
  exact ORRW.Support.insertion_inequality_of hd
    (ORRW.Frozen.max_exit (le_trans (by norm_num) hd))
    (ORRW.Frozen.resistance_packing hd)
