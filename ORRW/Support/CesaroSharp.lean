/-
The occupation display of Bou-Rabee--Peres, label `eq:cesaro` (orrw.tex:1102-1105):

  "Taking `m = 0` and `h = n` in (eq:occupation), and using `log(n+2) ≤ C n^{1/3}` when
   `d = 2`, gives, for every `n ≥ 1`,
     `sup_{z ∈ ℤ^d} ∑_{j=0}^{n-1} P_β{X_j = z} ≤ C (1 + (β-1)^{d/(d+1)}) n^{1/(d+1)}`."

The supremum over sites is a universal quantifier over sites inside the scope of the constant
(ruling R-006), and the probabilities are those of the walk at a horizon `M ≥ n`, as in
`ORRW.Frozen.occupation_cesaro`. The proof is the paper's: the interval estimate
`ORRW.Frozen.occupation` with `m = 0` and `h = n`, and `ORRW.H_le_rpow` for the logarithm.
-/
import ORRW.Basic
import ORRW.Support.Occupation
import ORRW.Frozen.Occupation.Occupation

open ORRW Finset

/-- **The occupation display `eq:cesaro`.** For `d ≥ 2` there is a constant `C` such that for
every `β ≥ 1`, every `n ≥ 1`, every horizon `M ≥ n` and every site `z`, the expected number of
visits to `z` before time `n` is at most `C (1 + (β-1)^{d/(d+1)}) n^{1/(d+1)}`. -/
theorem ORRW.occupation_cesaro_sharp (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β → ∀ N : ℕ, 1 ≤ N → ∀ M : ℕ, N ≤ M → ∀ z : ORRW.Site d,
      ∑ j ∈ Finset.range N, ORRW.prb (d := d) M β (fun w => ORRW.pos w j = z)
        ≤ C * (1 + (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1))) * (N : ℝ) ^ (1 / ((d : ℝ) + 1)) := by
  obtain ⟨C, hC⟩ := ORRW.Frozen.occupation d hd
  refine ⟨6 * max C 0, fun β hβ N hN M hM z => ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmain := hC β hβ z 0 N hN M (by omega)
  have hrange : Finset.Ico 0 (0 + N) = Finset.range N := by
    rw [zero_add, Finset.range_eq_Ico]
  rw [hrange] at hmain
  have hH := ORRW.H_le_rpow d hd hN
  set H : ℝ := if d = 2 then Real.log ((N : ℝ) + 2) else 1 with hHdef
  set B : ℝ := (β - 1) ^ ((d : ℝ) / ((d : ℝ) + 1)) with hBdef
  set P : ℝ := (N : ℝ) ^ (1 / ((d : ℝ) + 1)) with hPdef
  have hPnn : 0 ≤ P := Real.rpow_nonneg hNpos.le _
  have hBnn : 0 ≤ B := Real.rpow_nonneg (by linarith) _
  have hHnn : 0 ≤ H := by
    rw [hHdef]
    split_ifs
    · exact Real.log_nonneg (by linarith)
    · norm_num
  have hM0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hCle : C * (H + B * P) ≤ max C 0 * (H + B * P) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  calc ∑ j ∈ Finset.range N, ORRW.prb (d := d) M β (fun w => ORRW.pos w j = z)
      ≤ max C 0 * (H + B * P) := le_trans hmain hCle
    _ ≤ max C 0 * (6 * P + 6 * (B * P)) :=
        mul_le_mul_of_nonneg_left (by linarith [hH, mul_nonneg hBnn hPnn]) hM0
    _ = 6 * max C 0 * (1 + B) * P := by ring
