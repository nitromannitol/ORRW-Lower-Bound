/-
The almost-sure layer: transferring a fixed-time bound to the infinite-path
measure, and the Borel-Cantelli step that turns a summable tail into an
almost-sure statement.

`ORRW.pathMeasure_event` is the transfer.  With it, every bound the paper proves
about `ORRW.prb` at a fixed time becomes a bound about one measure that covers
all times at once, which is what an almost-sure claim needs.
-/
import ORRW.Support.InfinitePath
import ORRW.Support.Occupation
import ORRW.Frozen.AlmostSure.PathMeasureBridge

open MeasureTheory ProbabilityTheory Finset Preorder Filter Real Asymptotics
open scoped ENNReal

namespace ORRW

variable {d : ℕ}

/-- The initial weights normalise. -/
theorem sum_initPMF (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) :
    ∑ a : Dir d, initPMF β a = 1 := by
  have htpos := ORRW.totalWeight_pos (n := 0) hd hβ (fun i => i.elim0) 0
  have hw : ∀ a ∈ (Finset.univ : Finset (Dir d)),
      0 ≤ ORRW.stepWeight β (d := d) (n := 0) (fun i => i.elim0) 0 a := by
    intro a _; unfold ORRW.stepWeight; split <;> linarith
  unfold initPMF
  rw [← ENNReal.ofReal_sum_of_nonneg
      (fun a _ => div_nonneg (hw a (Finset.mem_univ a)) (le_of_lt htpos))]
  rw [← Finset.sum_div]
  show ENNReal.ofReal
      (ORRW.totalWeight β (d := d) (n := 0) (fun i => i.elim0) 0 /
        ORRW.totalWeight β (d := d) (n := 0) (fun i => i.elim0) 0) = 1
  rw [div_self (ne_of_gt htpos), ENNReal.ofReal_one]

/-- Provides the probability-measure structure on the infinite-path space so that almost-sure statements about the walk are meaningful. -/
instance isProbabilityMeasure_initMeasure [hd : Fact (0 < d)] {β : ℝ} [hβ : Fact (1 ≤ β)] :
    IsProbabilityMeasure (initMeasure (d := d) β) := by
  refine ⟨?_⟩
  rw [initMeasure, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact sum_initPMF hd.out hβ.out

/-- Provides the probability measure on infinite trajectories that the almost-sure layer needs, normalized at the initial site. -/
instance isProbabilityMeasure_initTraj [Fact (0 < d)] {β : ℝ} [Fact (1 ≤ β)] :
    IsProbabilityMeasure (initTraj (d := d) β) := by
  rw [initTraj]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The path measure on infinite walks is a probability measure, so the almost-sure statements built from fixed-time bounds are stated with respect to a genuine measure. -/
instance isProbabilityMeasure_pathMeasure [Fact (0 < d)] {β : ℝ} [Fact (1 ≤ β)] :
    IsProbabilityMeasure (pathMeasure (d := d) β) := by
  rw [pathMeasure]
  infer_instance

/-- The inverse of `ofPrefix`: read an `n+1`-letter word as an `Iic n`-indexed one. -/
def toPrefix (n : ℕ) (w : Fin (n + 1) → Dir d) : Π _i : Iic n, Dir d :=
  fun i => w ⟨i.1, Nat.lt_succ_of_le (mem_Iic.1 i.2)⟩

/-- Bridges the fixed-time probability of a walk prefix to the corresponding event under the infinite-path measure, enabling the transfer of fixed-time bounds to almost-sure statements. -/
theorem ofPrefix_toPrefix (n : ℕ) (w : Fin (n + 1) → Dir d) :
    ofPrefix n (toPrefix n w) = w := by
  funext i; rfl

/-- A direction assignment on the range up to time n that is a prefix of a later one is already a prefix at time n, used to compare path measures across truncations. -/
theorem toPrefix_ofPrefix (n : ℕ) (x : Π _i : Iic n, Dir d) :
    toPrefix n (ofPrefix n x) = x := by
  funext i; rfl

/-- The cylinder of an `n`-letter word, for every `n`. -/
theorem pathMeasure_ofPath [Fact (0 < d)] {β : ℝ} [Fact (1 ≤ β)] (n : ℕ)
    (w : Fin n → Dir d) :
    pathMeasure (d := d) β {ω | ofPath n ω = w} = ENNReal.ofReal (prob β w) := by
  cases n with
  | zero =>
    have hset : {ω : Π _k : ℕ, Dir d | ofPath 0 ω = w} = Set.univ := by
      ext ω; simp [Subsingleton.elim (ofPath 0 ω) w]
    rw [hset, measure_univ]
    simp [prob]
  | succ m =>
    have hset : {ω : Π _k : ℕ, Dir d | ofPath (m + 1) ω = w}
        = {ω | restr m ω = toPrefix m w} := by
      ext ω
      simp only [Set.mem_setOf_eq, ofPath_restr]
      constructor
      · intro h; rw [← h, toPrefix_ofPrefix]
      · intro h; rw [h, ofPrefix_toPrefix]
    rw [hset, ORRW.Frozen.pathMeasure_restr (β := β) m (toPrefix m w), ofPrefix_toPrefix]

/-- Evaluating the first n steps of an infinite walk is a measurable map, so events on finite prefixes can be transferred to the infinite-path measure. -/
theorem measurable_ofPath (n : ℕ) : Measurable (ofPath (d := d) n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

open Classical in
/-- **The transfer.**  Any event of the first `n` steps has the same probability
under the infinite-path measure as under the finite-word law.  This is what lets
a fixed-time bound of the paper be used at every time at once. -/
theorem pathMeasure_event [hd : Fact (0 < d)] {β : ℝ} [hβ : Fact (1 ≤ β)] (n : ℕ)
    (P : (Fin n → Dir d) → Prop) :
    pathMeasure (d := d) β {ω | P (ofPath n ω)} = ENNReal.ofReal (prb n β P) := by
  have hset : {ω : Π _k : ℕ, Dir d | P (ofPath n ω)}
      = ⋃ w ∈ (Finset.univ.filter (fun w : Fin n → Dir d => P w)),
          {ω | ofPath n ω = w} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, exists_prop]
    exact ⟨fun h => ⟨ofPath n ω, h, rfl⟩, fun ⟨w, hw, he⟩ => he ▸ hw⟩
  rw [hset, measure_biUnion_finset]
  · rw [prb]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun w : Fin n → Dir d => P w) (fun w => prob β w * (if P w then 1 else 0))]
    have hzero : ∑ w ∈ Finset.univ.filter (fun w : Fin n → Dir d => ¬ P w),
        prob β w * (if P w then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun w hw => by
        simp [(Finset.mem_filter.1 hw).2]
    rw [hzero, add_zero]
    have hone : ∀ w ∈ Finset.univ.filter (fun w : Fin n → Dir d => P w),
        prob β w * (if P w then 1 else 0) = prob β w :=
      fun w hw => by simp [(Finset.mem_filter.1 hw).2]
    rw [Finset.sum_congr rfl hone,
      ENNReal.ofReal_sum_of_nonneg (fun w _ => prob_nonneg hd.out hβ.out w)]
    exact Finset.sum_congr rfl fun w _ => pathMeasure_ofPath n w
  · intro u _ v _ huv
    refine Set.disjoint_left.2 fun ω hu hv => huv ?_
    have h1 : ofPath n ω = u := hu
    have h2 : ofPath n ω = v := hv
    exact h1.symm.trans h2
  · intro w _
    exact measurableSet_eq_fun (measurable_ofPath n) measurable_const

set_option maxHeartbeats 1000000 in
/-- A stretched-exponential tail is summable: this is what turns the paper's
Theorem (stretched-exponential tail) into an almost-sure statement. -/
theorem summable_exp_neg_rpow {c α : ℝ} (hc : 0 < c) (hα : 0 < α) :
    Summable (fun n : ℕ => Real.exp (-(c * (n : ℝ) ^ α))) := by
  -- eventually `2 log x ≤ c * x ^ α`, because `log` is `o` of any positive power
  have hlo : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x ^ α) :=
    isLittleO_log_rpow_atTop hα
  have hev := hlo.def (by positivity : 0 < c / 2)
  rw [eventually_atTop] at hev
  obtain ⟨X, hX⟩ := hev
  obtain ⟨N, hN⟩ := exists_nat_ge (max X 1)
  -- past `N` the terms are dominated by `1 / n ^ 2`
  have hdom : ∀ n : ℕ, Real.exp (-(c * ((n + N : ℕ) : ℝ) ^ α)) ≤ 1 / ((n + N : ℕ) : ℝ) ^ (2 : ℝ) := by
    intro n
    have hn1 : (1 : ℝ) ≤ ((n + N : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_max_right X 1) hN
      have : (N : ℝ) ≤ ((n + N : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
      linarith
    have hnX : X ≤ ((n + N : ℕ) : ℝ) := by
      have : X ≤ (N : ℝ) := le_trans (le_max_left X 1) hN
      have : (N : ℝ) ≤ ((n + N : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
      linarith
    have hpos : (0 : ℝ) < ((n + N : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hn1
    have hb := hX _ hnX
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hpos.le _)] at hb
    have hlog : Real.log ((n + N : ℕ) : ℝ) ≤ (c / 2) * ((n + N : ℕ) : ℝ) ^ α :=
      le_trans (le_abs_self _) hb
    have hkey : (2 : ℝ) * Real.log ((n + N : ℕ) : ℝ) ≤ c * ((n + N : ℕ) : ℝ) ^ α := by linarith
    have : Real.exp (-(c * ((n + N : ℕ) : ℝ) ^ α))
        ≤ Real.exp (-(2 * Real.log ((n + N : ℕ) : ℝ))) := by
      rw [Real.exp_le_exp]; linarith
    refine le_trans this (le_of_eq ?_)
    have hrw : -(2 * Real.log ((n + N : ℕ) : ℝ))
        = Real.log (((n + N : ℕ) : ℝ) ^ (-2 : ℝ)) := by
      rw [Real.log_rpow hpos]; ring
    rw [hrw, Real.exp_log (Real.rpow_pos_of_pos hpos _), Real.rpow_neg hpos.le, one_div]
  refine (summable_nat_add_iff N).1 ?_
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hdom ?_
  exact ((summable_nat_add_iff N).2 (summable_one_div_nat_rpow.2 (by norm_num))).congr
    (fun n => rfl)

end ORRW
