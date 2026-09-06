/-
Frozen statement of the paper's almost-sure range bound.

`orrw.tex`: "The right-hand side is summable in `n` for each fixed
`beta`, so the Borel-Cantelli lemma turns Theorem (stretched-exponential tail)
into the almost sure bound
  `liminf_{n -> infty} |R_n| n^{-d/(d+1)} >= c beta^{-d/(d+1)}`."

This is the first of the two claims that ruling R-001 could not express, because
it is about all times at once.  It is stated against `ORRW.pathMeasure`, the law
of the walk on infinite direction words, whose marginals are `ORRW.prob` by the
node `bridge-path-measure`.

Modelling decisions.

* Ruling A-003 (`liminf` as an eventual bound).  The paper's
  `liminf |R_n| n^{-e} >= c b^{-e}` is rendered as: almost surely, for all large
  `n`, `c b^{-e} n^e <= |R_n|`.  This is the form Borel-Cantelli produces and
  the one a reader can use without unfolding `liminf`, and it is *stronger* than
  the paper's: eventually `A <= X_n` gives `liminf X_n >= A`, but not conversely,
  since `X_n = A - 1/n` has `liminf X_n = A` while `A <= X_n` never holds.  So
  the statement proved here implies the paper's and is not implied by it.

* Ruling A-002 (`Fact` hypotheses), as in `bridge-path-measure`.
-/
import ORRW.Support.AlmostSure
import ORRW.Frozen.RangeTail

open MeasureTheory ProbabilityTheory Finset Preorder Filter Real Asymptotics
open scoped ENNReal

open ORRW in
set_option maxHeartbeats 2000000 in
-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.range_ae {d : ℕ} [hd0 : Fact (0 < d)] (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 1 ≤ β),
      ∀ᵐ ω ∂(@ORRW.pathMeasure d hd0 β ⟨hβ⟩), ∀ᶠ n : ℕ in atTop,
        c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))
          ≤ ((ORRW.R (ORRW.ofPath n ω) n).card : ℝ)
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨c, C, hc, hC, htail⟩ := ORRW.Frozen.range_tail d hd
  refine ⟨c, hc, ?_⟩
  intro β hβ
  haveI : Fact (1 ≤ β) := ⟨hβ⟩
  set e : ℝ := (d : ℝ) / ((d : ℝ) + 1) with he
  set α : ℝ := ((d : ℝ) - 1) / ((d : ℝ) + 1) with hα
  have hd1 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hαpos : 0 < α := by
    rw [hα]; apply div_pos <;> [linarith; linarith]
  set Bad : ℕ → Set (Π _k : ℕ, Dir d) := fun n =>
    if C * β ≤ (n : ℝ) then
      {ω | ((R (ofPath n ω) n).card : ℝ) < c * β ^ (-e) * (n : ℝ) ^ e} else ∅ with hBad
  -- each bad event is bounded by the tail
  have hmeas : ∀ n, pathMeasure (d := d) β (Bad n)
      ≤ ENNReal.ofReal (Real.exp (-(c * β ^ (-α) * (n : ℝ) ^ α))) := by
    intro n
    rw [hBad]
    by_cases hn : C * β ≤ (n : ℝ)
    · simp only [hn, if_true]
      have heq := pathMeasure_event (d := d) (β := β) n
        (fun w : Fin n → Dir d => ((R w n).card : ℝ) < c * β ^ (-e) * (n : ℝ) ^ e)
      rw [heq]
      refine le_trans (ENNReal.ofReal_le_ofReal (htail β hβ n hn)) (le_of_eq ?_)
      congr 2
      rw [Real.div_rpow (by positivity) (by linarith), Real.rpow_neg (by linarith)]
      field_simp
    · simp only [hn, if_false, measure_empty]
      exact zero_le _
  -- and the bound is summable
  have hsum : ∑' n, pathMeasure (d := d) β (Bad n) ≠ ⊤ := by
    have hcb : 0 < c * β ^ (-α) := by
      have : (0:ℝ) < β ^ (-α) := Real.rpow_pos_of_pos (by linarith) _
      positivity
    have hS := ORRW.summable_exp_neg_rpow hcb hαpos
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hmeas)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le) hS]
    exact ENNReal.ofReal_ne_top
  -- Borel-Cantelli
  have hzero := MeasureTheory.measure_limsup_atTop_eq_zero (μ := pathMeasure (d := d) β) hsum
  refine (MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hzero).mono fun ω hω => ?_
  rw [Filter.mem_limsup_iff_frequently_mem, Filter.not_frequently] at hω
  have hev : ∀ᶠ n : ℕ in atTop, C * β ≤ (n : ℝ) :=
    Filter.eventually_atTop.2 ⟨⌈C * β⌉₊, fun n hn => le_trans (Nat.le_ceil _) (by exact_mod_cast hn)⟩
  filter_upwards [hω, hev] with n hn hnC
  rw [hBad] at hn
  simp only [hnC, if_true, Set.mem_setOf_eq, not_lt] at hn
  exact hn

