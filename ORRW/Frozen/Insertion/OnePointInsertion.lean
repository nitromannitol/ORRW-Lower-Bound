/-
Frozen statement of the one-point insertion lemma of Bou-Rabee--Peres,
*Once-reinforced random walk on `ℤ^d` has range exponent at least `d/(d+1)`*,
Section 2, Lemma (Adding one vertex), label `lem:schur`, `orrw.tex:493-514`:

  "Let `d ≥ 1`, let `A ⊂ ℤ^d` be finite, let `x ∉ A`, and set `A⁺ := A ∪ {x}`.
   Give every edge of `ℤ^d` unit conductance and let `Reff(x ↔ (A⁺)^c)` be the
   effective resistance between `x` and the grounded complement of `A⁺`.  Then
     `Reff(x ↔ (A⁺)^c) = -Δ_{A⁺}^{-1}(x,x) ≥ 1/(2d)`,
     `u_{A⁺}(x) = Reff(x ↔ (A⁺)^c) h_A(x)`,
   and
     `T(A⁺) - T(A) = h_A(x) u_{A⁺}(x)`."

Modelling decisions.

* Ruling F-201 (the Schur identity is the definition).  `ORRW.Reff A x` is
  *defined* in `ORRW/Lattice.lean` (ruling L-002) to be `-Δ_{A⁺}^{-1}(x,x)`,
  which is the first equality of `eq:schur`.  That equality is therefore true
  by definition here and is not restated; the electrical-network content of
  `eq:schur` is not formalized.  What remains of the lemma, and is frozen
  below, is the identity `u_{A⁺}(x) = Reff · h_A(x)`, the identity `eq:deltaT`
  for `T(A⁺) - T(A)`, the lower bound `Reff ≥ 1/(2d)`, and both consequences
  collected in `eq:hbound`.

* Ruling F-202 (`A⁺`).  `A⁺ = A ∪ {x}` is rendered as `insert x A`.

* Ruling F-203 (`eq:hbound` is part of the statement).  Both identities of
  `eq:hbound` follow from the other three assertions by algebra, but the paper
  states them as part of this lemma and uses them at `orrw.tex`, `660` and
  `670`, so they are asserted here rather than left to the reader.
-/
import ORRW.Lattice
import ORRW.Support.Insertion

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.one_point_insertion {d : ℕ} (hd : 1 ≤ d)
    (A : Finset (Site d)) (x : Site d) (hx : x ∉ A) :
    u (insert x A) x = Reff A x * h A x ∧
      T (insert x A) - T A = h A x * u (insert x A) x ∧
      1 / (2 * (d : ℝ)) ≤ Reff A x ∧
      h A x ^ 2 ≤ 2 * (d : ℝ) * (T (insert x A) - T A) ∧
      u (insert x A) x ^ 2 = Reff A x * (T (insert x A) - T A)
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨hu, hT, hR⟩ := ORRW.Support.one_point_insertion hd A x hx
  have hdpos : (0 : ℝ) < 2 * (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  refine ⟨hu, hT, hR, ?_, ?_⟩
  · -- `T(A⁺) - T(A) = Reff · h²`, and `Reff ≥ 1/(2d)`
    have hTh : T (insert x A) - T A = Reff A x * h A x ^ 2 := by
      rw [hT, hu]; ring
    have hstep : (1 / (2 * (d : ℝ))) * h A x ^ 2 ≤ Reff A x * h A x ^ 2 :=
      mul_le_mul_of_nonneg_right hR (sq_nonneg _)
    rw [hTh]
    calc h A x ^ 2 = 2 * (d : ℝ) * ((1 / (2 * (d : ℝ))) * h A x ^ 2) := by field_simp
      _ ≤ 2 * (d : ℝ) * (Reff A x * h A x ^ 2) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt hdpos)
  · rw [hT, hu]; ring
