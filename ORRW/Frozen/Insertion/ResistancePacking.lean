/-
Frozen statement of the resistance packing lemma of Bou-Rabee--Peres,
*Once-reinforced random walk on `ℤ^d` has range exponent at least `d/(d+1)`*,
Section 2, Lemma (Sum of effective resistances), label `lem:packing`, `orrw.tex:485-492`:

  "Let `d ≥ 2`, let `M ≥ 1` be an integer, let `x_1, …, x_M` be distinct
   vertices of `ℤ^d`, and let `A_i := {x_1, …, x_i}` for `1 ≤ i ≤ M`.  Then
     `∑_{i=1}^M Reff(x_i ↔ A_i^c) ≤ CM`."

Modelling decisions.

* Ruling F-301 (the insertion order).  The list `x_1, …, x_M` of distinct
  vertices is an injective `x : Fin M → Site d`, and the paper's `A_i` for the
  `0`-indexed step `i` is `insert (x i) ((Finset.Iio i).image x)`.  Since
  `ORRW.Reff A y` is by construction the resistance from `y` to the complement
  of `insert y A`, the paper's `Reff(x_i ↔ A_i^c)` is
  `Reff ((Finset.Iio i).image x) (x i)`; the argument passed to `Reff` is the
  set of *strictly earlier* vertices.

* Ruling F-302 (order of quantifiers).  `C` depends only on `d`, so it is bound
  before `M` and before `x`.

* Ruling F-303 (`0 < C`).  Positivity of `C` is asserted.

* Ruling F-304 (`M ≥ 1`).  The paper's hypothesis is kept even though the case
  `M = 0` is an empty sum.
-/
import ORRW.Lattice
import ORRW.Support.Thomson

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.resistance_packing {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → ∀ x : Fin M → Site d, Function.Injective x →
      ∑ i : Fin M, Reff ((Finset.Iio i).image x) (x i) ≤ C * (M : ℝ)
-- FROZEN-STATEMENT-END
:= by exact ORRW.Support.resistance_packing_aux hd
