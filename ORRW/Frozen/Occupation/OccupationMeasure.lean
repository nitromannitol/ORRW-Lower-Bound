/-
Theorem 1.3 of `orrw.tex`, frozen.

Paper line encoded, `NOT` (label `thm:occupation-intro`,
equation `eq:occupation-intro`):

  "Theorem (Occupation measure).  Let $d\\geq2$.  There is a constant $C<\\infty$,
   depending only on $d$, such that for every $\\beta\\geq1$ and every integer
   $n\\geq1$, $\\sup_{z\\in\\Z^d}\\E_\\beta L_n(z)\\leq C\\beta n^{1/(d+1)}$."

Ruling R-006.  `L_n(z) = #{0 <= j < n : X_j = z}` is the occupation measure of
`z`.  Under ruling R-001 its expectation is the finite sum
`∑_{j<n} prb N β (pos · j = z)` at any horizon `N >= n`; the horizon is
universally quantified rather than fixed, and `n <= N` is load-bearing because a
word freezes the walk past its own length.  The `sup` over `z` is rendered as a
universal quantifier, which is the same assertion and avoids an `sSup` junk value
on an unbounded family.
-/
import ORRW.Basic
import ORRW.Support.Occupation
import ORRW.Frozen.Occupation.Occupation

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.occupation_measure (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, 1 ≤ n → ∀ N : ℕ, n ≤ N → ∀ z : ORRW.Site d,
      ∑ j ∈ Finset.range n, ORRW.prb (d := d) N β (fun w => ORRW.pos w j = z)
        ≤ C * β * (n : ℝ) ^ (1 / ((d : ℝ) + 1))
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨C, hC⟩ := ORRW.Frozen.occupation d hd
  refine ⟨7 * max C 0, fun β hβ n hn N hN z => ?_⟩
  -- `eq:occupation` at `m = 0`, `h = n`; the window `Ico 0 n` is `range n`.
  have hmain := hC β hβ z 0 n hn N (by omega)
  have hrange : Finset.Ico 0 (0 + n) = Finset.range n := by
    rw [zero_add, Finset.range_eq_Ico]
  rw [hrange] at hmain
  refine le_trans hmain ?_
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hPnn : (0 : ℝ) ≤ (n : ℝ) ^ (1 / ((d : ℝ) + 1)) :=
    Real.rpow_nonneg (le_of_lt hnpos) _
  -- `log(n+2) ≤ 6 n^{1/(d+1)}`, and `1 ≤ n^{1/(d+1)}` in the `d ≥ 3` branch.
  have hH := ORRW.H_le_rpow d hd hn
  -- `(β-1)^{d/(d+1)} ≤ β`.
  have hS : (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) * (n : ℝ) ^ (1 / ((d : ℝ) + 1))
      ≤ β * (n : ℝ) ^ (1 / ((d : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (ORRW.rpow_sub_one_le d hβ) hPnn
  have hHnn : (0 : ℝ) ≤ (if d = 2 then Real.log ((n : ℝ) + 2) else 1) := by
    by_cases h2 : d = 2
    · rw [if_pos h2]
      exact Real.log_nonneg (by linarith)
    · rw [if_neg h2]; norm_num
  have hSnn : (0 : ℝ) ≤ (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) * (n : ℝ) ^ (1 / ((d : ℝ) + 1)) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) hPnn
  have hM0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hCle : C * ((if d = 2 then Real.log ((n : ℝ) + 2) else 1)
        + (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) * (n : ℝ) ^ (1 / ((d : ℝ) + 1)))
      ≤ max C 0 * ((if d = 2 then Real.log ((n : ℝ) + 2) else 1)
        + (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) * (n : ℝ) ^ (1 / ((d : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  refine le_trans hCle ?_
  -- `6 n^e + β n^e ≤ 7 β n^e` because `β ≥ 1`.
  have hbr : (if d = 2 then Real.log ((n : ℝ) + 2) else 1)
        + (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) * (n : ℝ) ^ (1 / ((d : ℝ) + 1))
      ≤ 7 * β * (n : ℝ) ^ (1 / ((d : ℝ) + 1)) := by
    have h6 : (0 : ℝ) ≤ 6 * (β - 1) * (n : ℝ) ^ (1 / ((d : ℝ) + 1)) :=
      mul_nonneg (by linarith) hPnn
    nlinarith [hH, hS, h6]
  calc max C 0 * ((if d = 2 then Real.log ((n : ℝ) + 2) else 1)
          + (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) * (n : ℝ) ^ (1 / ((d : ℝ) + 1)))
      ≤ max C 0 * (7 * β * (n : ℝ) ^ (1 / ((d : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hbr hM0
    _ = 7 * max C 0 * β * (n : ℝ) ^ (1 / ((d : ℝ) + 1)) := by ring

