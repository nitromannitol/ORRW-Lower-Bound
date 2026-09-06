/-
Supporting lemmas for `ORRW.Frozen.exponents_optimal` (`prop:beta-sharp`,
`orrw.tex`).

The proof of `eq:range-upper` here is the paper's, with one substitution.  The
paper bounds `|R_n|` through `|R_n| ≤ 1 + |E_n|`, which is the connectivity of
the traversed subgraph; the same estimate is reached without it, since a step
that reaches an unvisited site must cross an untraversed edge: both endpoints of
a traversed edge are visited (`ORRW.mem_E_endpoint`).  So the range grows by at
most one at each step, and only when the step crosses an untraversed edge.  Past
the first step the walk stands at a site with at least one traversed incident
edge, so at most `2d - 1` of its `2d` incident edges are untraversed
(`nu_lt_two_mul`) and the normalizer is at least `β`; the chance of crossing an
untraversed edge is therefore at most `2d/β` (`nu_div_mu_le`), which is the
paper's `j/(j + β(2d-j)) ≤ (2d-1)/(2d-1+β) ≤ 2d/β`.  Nothing in this file is
frozen.
-/
import ORRW.Potential
import ORRW.Support.Return
import ORRW.Support.TimeCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

/-- Flipping the sign bit of a direction negates its vector. -/
theorem dirVec_not {d : ℕ} (c : Fin d) (b : Bool) :
    dirVec ((c, !b) : Dir d) = -dirVec ((c, b) : Dir d) := by
  cases b
  · funext j; simp only [dirVec, Pi.neg_apply]; split <;> norm_num
  · exact dirVec_neg c

/-- The range after one more step. -/
theorem R_snoc_succ {d m : ℕ} (v : Fin m → Dir d) (a : Dir d) :
    R (Fin.snoc v a) (m + 1) = insert (pos v m + dirVec a) (R v m) := by
  classical
  have hposi : ∀ k, k ≤ m → pos (Fin.snoc v a) k = pos v k := by
    intro k hk
    rw [← pos_init (Fin.snoc v a) hk, Fin.init_snoc]
  have hlast : pos (Fin.snoc v a) (m + 1) = pos v m + dirVec a := by
    rw [pos_succ (Fin.snoc v a) m (Nat.lt_succ_self m), hposi m le_rfl]
    have hsl : (Fin.snoc v a : Fin (m + 1) → Dir d) (Fin.last m) = a := by simp
    exact congrArg (fun z => pos v m + dirVec z) hsl
  have himg : (Finset.range (m + 1)).image (pos (Fin.snoc v a)) = R v m := by
    refine Finset.image_congr ?_
    intro k hk
    exact hposi k (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_coe.mp hk)))
  show (Finset.range (m + 1 + 1)).image (pos (Fin.snoc v a)) = _
  rw [Finset.range_add_one, Finset.image_insert, hlast, himg]

/-- After at least one step the walk stands at a site with a traversed incident
edge, so at most `2d - 1` of its incident edges are untraversed. -/
theorem nu_lt_two_mul {d m : ℕ} (hd : 0 < d) (hm : 1 ≤ m) (v : Fin m → Dir d) :
    nu v m < 2 * d := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  set e : Dir d := v ⟨j, Nat.lt_succ_self j⟩ with he
  set fl : Dir d := (e.1, !e.2) with hfl
  have hstep : pos v (j + 1) = pos v j + dirVec e := pos_succ v j (Nat.lt_succ_self j)
  have hneg : dirVec fl = -dirVec e := by
    have h := dirVec_not e.1 e.2
    rw [hfl]
    simpa using h
  have hback : pos v (j + 1) + dirVec fl = pos v j := by
    rw [hstep, hneg]; abel
  have hmem : s(pos v (j + 1), pos v (j + 1) + dirVec fl) ∈ E v (j + 1) := by
    rw [hback, Sym2.eq_swap]
    simp only [E]
    exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by simp))
  have hsub : (univ.filter (fun a : Dir d =>
      s(pos v (j + 1), pos v (j + 1) + dirVec a) ∉ E v (j + 1))) ⊆ univ.erase fl := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
    rintro rfl
    exact (Finset.mem_filter.mp hx).2 hmem
  have hcu : (Finset.univ : Finset (Dir d)).card = 2 * d := by
    rw [Finset.card_univ]
    simp [Fintype.card_prod]
    omega
  calc nu v (j + 1) ≤ ((Finset.univ : Finset (Dir d)).erase fl).card :=
        Finset.card_le_card hsub
    _ = 2 * d - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), hcu]
    _ < 2 * d := by omega

/-- The chance of crossing an untraversed edge, at any step past the first. -/
theorem nu_div_mu_le {d m : ℕ} (hd : 0 < d) (hm : 1 ≤ m) {β : ℝ} (hβ : 1 ≤ β)
    (v : Fin m → Dir d) : (nu v m : ℝ) / mu β v m ≤ 2 * (d : ℝ) / β := by
  have hβ0 : (0 : ℝ) < β := lt_of_lt_of_le one_pos hβ
  have hnu : (nu v m : ℝ) + 1 ≤ 2 * (d : ℝ) := by
    have := nu_lt_two_mul hd hm v
    have h2 : (nu v m) + 1 ≤ 2 * d := this
    exact_mod_cast h2
  have hnu0 : (0 : ℝ) ≤ (nu v m : ℝ) := Nat.cast_nonneg _
  have hmu : β ≤ mu β v m := by
    unfold mu
    nlinarith
  have hmupos : (0 : ℝ) < mu β v m := lt_of_lt_of_le hβ0 hmu
  rw [div_le_div_iff₀ hmupos hβ0]
  nlinarith

/-- The one-step bound: past the first step the expected number of new sites is
at most `2d/β`. -/
theorem range_one_step {d m : ℕ} (hd : 0 < d) (hm : 1 ≤ m) {β : ℝ} (hβ : 1 ≤ β)
    (v : Fin m → Dir d) :
    (∑ a : Dir d, stepWeight β v m a * ((R (Fin.snoc v a) (m + 1)).card : ℝ))
        / totalWeight β v m
      ≤ ((R v m).card : ℝ) + 2 * (d : ℝ) / β := by
  classical
  set A : Finset (Dir d) :=
    univ.filter (fun a : Dir d => s(pos v m, pos v m + dirVec a) ∉ E v m) with hA
  have hAnu : A.card = nu v m := rfl
  have htwpos : (0 : ℝ) < totalWeight β v m := totalWeight_pos hd hβ v m
  have h1 : ∀ a : Dir d, stepWeight β v m a * ((R (Fin.snoc v a) (m + 1)).card : ℝ)
      ≤ stepWeight β v m a * ((R v m).card : ℝ) + (if a ∈ A then (1 : ℝ) else 0) := by
    intro a
    rw [R_snoc_succ]
    by_cases ha : a ∈ A
    · have hnot : s(pos v m, pos v m + dirVec a) ∉ E v m := (Finset.mem_filter.mp ha).2
      have hsw : stepWeight β v m a = 1 := by unfold stepWeight; rw [if_neg hnot]
      rw [hsw, if_pos ha, one_mul, one_mul]
      have hc : ((insert (pos v m + dirVec a) (R v m)).card : ℝ) ≤ ((R v m).card : ℝ) + 1 := by
        exact_mod_cast Finset.card_insert_le (pos v m + dirVec a) (R v m)
      linarith
    · have hE : s(pos v m, pos v m + dirVec a) ∈ E v m := by
        by_contra hc
        exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hc⟩)
      have hmem : pos v m + dirVec a ∈ R v m :=
        mem_E_endpoint v hE (Sym2.mem_mk_right _ _)
      rw [Finset.insert_eq_self.mpr hmem, if_neg ha]
      linarith
  have hind : ∑ a : Dir d, (if a ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hbound : ∑ a : Dir d, stepWeight β v m a * ((R (Fin.snoc v a) (m + 1)).card : ℝ)
      ≤ ((R v m).card : ℝ) * totalWeight β v m + (nu v m : ℝ) := by
    calc ∑ a : Dir d, stepWeight β v m a * ((R (Fin.snoc v a) (m + 1)).card : ℝ)
        ≤ ∑ a : Dir d, (stepWeight β v m a * ((R v m).card : ℝ)
            + (if a ∈ A then (1 : ℝ) else 0)) := Finset.sum_le_sum fun a _ => h1 a
      _ = ((R v m).card : ℝ) * totalWeight β v m + (nu v m : ℝ) := by
          rw [Finset.sum_add_distrib, hind, hAnu, ← Finset.sum_mul]
          have htw : (∑ i : Dir d, stepWeight β v m i) = totalWeight β v m := rfl
          rw [htw]; ring
  have hnm : (nu v m : ℝ) ≤ 2 * (d : ℝ) / β * totalWeight β v m := by
    have h := nu_div_mu_le hd hm hβ v
    rw [mu_eq_totalWeight] at h
    rwa [div_le_iff₀ htwpos] at h
  rw [div_le_iff₀ htwpos]
  nlinarith

/-- Adding a constant inside an expectation. -/
theorem expect_add_const {d m : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β)
    (f : (Fin m → Dir d) → ℝ) (C : ℝ) :
    expect m β (fun v => f v + C) = expect m β f + C := by
  unfold expect
  have hterm : ∀ v : Fin m → Dir d, prob β v * (f v + C) = prob β v * f v + C * prob β v :=
    fun v => by ring
  rw [Finset.sum_congr rfl fun v _ => hterm v, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_prob_eq_one hd hβ m, mul_one]

/-- Upper bound on the expected range of the walk after m steps, feeding the optimal exponent estimate by charging each range increment to the crossing of an untraversed edge. -/
theorem expect_card_range_le_aux {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) (m : ℕ) :
    expect (d := d) (m + 1) β (fun w => ((R w (m + 1)).card : ℝ))
      ≤ 2 + 2 * (d : ℝ) * (m : ℝ) / β := by
  have hβ0 : (0 : ℝ) < β := lt_of_lt_of_le one_pos hβ
  induction m with
  | zero =>
      have h : expect 1 β (fun w : Fin 1 → Dir d => ((R w 1).card : ℝ)) = 2 := by
        unfold expect
        have hterm : ∀ w : Fin 1 → Dir d, prob β w * ((R w 1).card : ℝ) = prob β w * 2 := by
          intro w; rw [card_R_one w]; norm_num
        rw [Finset.sum_congr rfl fun w _ => hterm w, ← Finset.sum_mul, sum_prob_eq_one hd hβ 1,
          one_mul]
      rw [h]; norm_num
  | succ m ih =>
      have hstep : expect (m + 1 + 1) β (fun w => ((R w (m + 1 + 1)).card : ℝ))
          ≤ expect (m + 1) β (fun v => ((R v (m + 1)).card : ℝ) + 2 * (d : ℝ) / β) :=
        expect_succ_le hd hβ _ _ (fun v => range_one_step hd (Nat.succ_le_succ (Nat.zero_le m)) hβ v)
      rw [expect_add_const hd hβ] at hstep
      have harith : 2 + 2 * (d : ℝ) * (m : ℝ) / β + 2 * (d : ℝ) / β
          = 2 + 2 * (d : ℝ) * ((m : ℝ) + 1) / β := by field_simp; ring
      push_cast
      linarith [hstep, ih]

/-- `E_β|R_n| ≤ 2 + 2dn/β`, the paper's `eq:range-upper`. -/
theorem expect_card_range_le {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) {n : ℕ} (hn : 1 ≤ n) :
    expect (d := d) n β (fun w => ((R w n).card : ℝ)) ≤ 2 + 2 * (d : ℝ) * (n : ℝ) / β := by
  have hβ0 : (0 : ℝ) < β := lt_of_lt_of_le one_pos hβ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine le_trans (expect_card_range_le_aux hd hβ m) ?_
  have hkey : 2 * (d : ℝ) * (m : ℝ) / β ≤ 2 * (d : ℝ) * ((m : ℝ) + 1) / β := by
    rw [div_le_div_iff_of_pos_right hβ0]
    have : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
    nlinarith
  push_cast
  linarith

/-- A positive multiple of `n^e` bounded uniformly over `n ≥ 1` forces `e ≤ 0`. -/
theorem rpow_exponent_nonpos {e c C : ℝ} (hc : 0 < c)
    (h : ∀ n : ℕ, 1 ≤ n → c * (n : ℝ) ^ e ≤ C) : e ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  have ht : Filter.Tendsto (fun k : ℕ => ((k : ℝ)) ^ e) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hcon).comp tendsto_natCast_atTop_atTop
  obtain ⟨k, hk1, hk2⟩ :=
    ((ht.eventually_gt_atTop (C / c)).and (Filter.eventually_ge_atTop 1)).exists
  have h1 := h k hk2
  rw [div_lt_iff₀ hc] at hk1
  linarith

end ORRW
