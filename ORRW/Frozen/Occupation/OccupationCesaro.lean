/-
Time-averaged occupation corollary corresponding to the weaker C beta consequence
of label `eq:cesaro` (orrw.tex:1102-1105).

The current paper retains C (1 + (beta-1)^(d/(d+1))) in the unnormalized sum.
This frozen declaration retains the earlier C beta estimate for the average.
It follows from the dimension-specific interval estimate in `occupation`.
See VERIFICATION.md for the distinction.

The horizon M is at least the averaging window N, and the constant is quantified
before beta, N, M, and the site z. This expresses uniformity over those parameters.
-/
import ORRW.Basic
import ORRW.Support.Occupation
import ORRW.Frozen.Occupation.Occupation

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.occupation_cesaro (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β → ∀ N : ℕ, 1 ≤ N → ∀ M : ℕ, N ≤ M → ∀ z : ORRW.Site d,
      (1 / (N : ℝ)) * ∑ j ∈ Finset.range N,
          ORRW.prb (d := d) M β (fun w => ORRW.pos w j = z)
        ≤ C * β * (N : ℝ) ^ (-(d : ℝ) / ((d : ℝ) + 1))
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨C, hC⟩ := ORRW.Frozen.occupation d hd
  refine ⟨7 * max C 0, fun β hβ N hN M hM z => ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmain := hC β hβ z 0 N hN M (by omega)
  have hrange : Finset.Ico 0 (0 + N) = Finset.range N := by
    rw [zero_add, Finset.range_eq_Ico]
  rw [hrange] at hmain
  have hPnn : (0 : ℝ) ≤ (N : ℝ) ^ (1 / ((d : ℝ) + 1)) :=
    Real.rpow_nonneg (le_of_lt hNpos) _
  have hHnn : (0 : ℝ) ≤ (if d = 2 then Real.log ((N : ℝ) + 2) else 1) := by
    by_cases h2 : d = 2
    · rw [if_pos h2]
      exact Real.log_nonneg (by linarith)
    · rw [if_neg h2]; norm_num
  have hSnn : (0 : ℝ) ≤ (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) * (N : ℝ) ^ (1 / ((d : ℝ) + 1)) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) hPnn
  have hH := ORRW.H_le_rpow d hd hN
  have hS : (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) * (N : ℝ) ^ (1 / ((d : ℝ) + 1))
      ≤ β * (N : ℝ) ^ (1 / ((d : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (ORRW.rpow_sub_one_le d hβ) hPnn
  have hCle : C * ((if d = 2 then Real.log ((N : ℝ) + 2) else 1)
        + (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) * (N : ℝ) ^ (1 / ((d : ℝ) + 1)))
      ≤ max C 0 * ((if d = 2 then Real.log ((N : ℝ) + 2) else 1)
        + (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) * (N : ℝ) ^ (1 / ((d : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  have hM0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hbound : ∑ j ∈ Finset.range N, ORRW.prb (d := d) M β (fun w => ORRW.pos w j = z)
      ≤ max C 0 * (7 * β * (N : ℝ) ^ (1 / ((d : ℝ) + 1))) := by
    refine le_trans hmain (le_trans hCle ?_)
    refine mul_le_mul_of_nonneg_left ?_ hM0
    have hβ7 : (6 : ℝ) + β ≤ 7 * β := by linarith
    nlinarith [hH, hS, hPnn]
  have hkey : (N : ℝ) ^ (1 / ((d : ℝ) + 1)) / (N : ℝ)
      = (N : ℝ) ^ (-(d : ℝ) / ((d : ℝ) + 1)) := by
    have hne : ((d : ℝ) + 1) ≠ 0 := by positivity
    rw [show (-(d : ℝ) / ((d : ℝ) + 1)) = 1 / ((d : ℝ) + 1) - 1 from by field_simp; ring,
      Real.rpow_sub hNpos, Real.rpow_one]
  have hinv : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  calc (1 / (N : ℝ)) * ∑ j ∈ Finset.range N,
        ORRW.prb (d := d) M β (fun w => ORRW.pos w j = z)
      ≤ (1 / (N : ℝ)) * (max C 0 * (7 * β * (N : ℝ) ^ (1 / ((d : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left hbound (le_of_lt hinv)
    _ = 7 * max C 0 * β * ((N : ℝ) ^ (1 / ((d : ℝ) + 1)) / (N : ℝ)) := by ring
    _ = 7 * max C 0 * β * (N : ℝ) ^ (-(d : ℝ) / ((d : ℝ) + 1)) := by rw [hkey]
