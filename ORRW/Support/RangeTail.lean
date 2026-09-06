/-
Theorem 1.2 of Bou-Rabee--Peres (`thm:whp`, `orrw.tex`): the
stretched-exponential tail of the range.  With `K` the constant of
`prop:charge`, the choice `k := ⌊(n/(8Kβ))^{d/(d+1)}⌋` makes
`8Kβk^{1+1/d} ≤ n`, so `prop:tail` applies at the horizon `n`, and
`eq:sigma-range` together with `eq:edges-sites` turns the event `{σ_k > n}`
into `{|R_n| < k/d}`.

Nothing in this file is frozen.
-/
import ORRW.Support.RangeLower
import ORRW.Frozen.Tail.SigmaTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW.Support

open Finset ORRW

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
/-- `P_β{|R_n| < cβ^{-d/(d+1)}n^{d/(d+1)}} ≤ exp(-c(n/β)^{(d-1)/(d+1)})`. -/
theorem range_tail_of (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, C * β ≤ (n : ℝ) →
      prb (d := d) n β (fun w =>
          ((R w n).card : ℝ)
            < c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)))
        ≤ Real.exp (-(c * ((n : ℝ) / β) ^ (((d : ℝ) - 1) / ((d : ℝ) + 1)))) := by
  have hd1 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  obtain ⟨c₀, K, hc₀pos, hKpos, hST⟩ := ORRW.Frozen.sigma_tail d hd
  set e : ℝ := (d : ℝ) / ((d : ℝ) + 1) with he
  set f : ℝ := ((d : ℝ) - 1) / (d : ℝ) with hf
  set g : ℝ := ((d : ℝ) - 1) / ((d : ℝ) + 1) with hg
  have hepos : (0 : ℝ) < e := by rw [he]; positivity
  have hfpos : (0 : ℝ) < f := by rw [hf]; apply div_pos <;> linarith
  have hgpos : (0 : ℝ) < g := by rw [hg]; apply div_pos <;> linarith
  have hef : e * f = g := by
    rw [he, hf, hg]
    have h1 : (d : ℝ) ≠ 0 := by linarith
    have h2 : (d : ℝ) + 1 ≠ 0 := by linarith
    field_simp
  have hA : (0 : ℝ) < 8 * K := by linarith
  -- `B` is treated as an opaque positive constant from here on.
  obtain ⟨B, hB⟩ : ∃ x : ℝ, x = (8 * K) ^ e := ⟨_, rfl⟩
  have hBpos : (0 : ℝ) < B := by rw [hB]; exact Real.rpow_pos_of_pos hA e
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have hBinv : (8 * K) ^ (-e) = B⁻¹ := by rw [hB, Real.rpow_neg hA.le]
  have hDpos : (0 : ℝ) < (2 * B) ^ f := Real.rpow_pos_of_pos (by linarith) f
  have hdRpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hcpos : (0 : ℝ) < min (B⁻¹ / (2 * (d : ℝ))) (c₀ / (2 * B) ^ f) :=
    lt_min (div_pos (inv_pos.mpr hBpos) (by linarith)) (div_pos hc₀pos hDpos)
  refine ⟨min (B⁻¹ / (2 * (d : ℝ))) (c₀ / (2 * B) ^ f), 8 * K, hcpos, hA, ?_⟩
  obtain ⟨c, hc⟩ : ∃ x : ℝ, x = min (B⁻¹ / (2 * (d : ℝ))) (c₀ / (2 * B) ^ f) := ⟨_, rfl⟩
  rw [← hc]
  have hc1 : c ≤ B⁻¹ / (2 * (d : ℝ)) := by rw [hc]; exact min_le_left _ _
  have hc2 : c ≤ c₀ / (2 * B) ^ f := by rw [hc]; exact min_le_right _ _
  intro β hβ n hn
  have hβpos : (0 : ℝ) < β := lt_of_lt_of_le one_pos hβ
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hAB : (0 : ℝ) < 8 * K * β := by positivity
  have hABn : 8 * K * β ≤ (n : ℝ) := by linarith [hn]
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hAB hABn
  obtain ⟨a, ha⟩ : ∃ x : ℝ, x = ((n : ℝ) / (8 * K * β)) ^ e := ⟨_, rfl⟩
  have ha0 : (0 : ℝ) ≤ a := by rw [ha]; exact Real.rpow_nonneg (by positivity) e
  have hage1 : (1 : ℝ) ≤ a := by
    rw [ha]
    have hx : (1 : ℝ) ≤ (n : ℝ) / (8 * K * β) := (one_le_div hAB).mpr hABn
    have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hx hepos.le
    rwa [Real.one_rpow] at this
  obtain ⟨k, hk⟩ : ∃ m : ℕ, m = ⌊a⌋₊ := ⟨_, rfl⟩
  have hk1 : 1 ≤ k := by rw [hk]; exact Nat.one_le_floor_iff a |>.mpr hage1
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkle : (k : ℝ) ≤ a := by rw [hk]; exact Nat.floor_le (by linarith)
  have hkge : a / 2 ≤ (k : ℝ) := by rw [hk]; exact half_le_floor hage1
  -- `8Kβk^{1+1/d} ≤ n`.
  have hexpo : e * (1 + (1 : ℝ) / (d : ℝ)) = 1 := by
    rw [he]
    have hd0 : (d : ℝ) ≠ 0 := by linarith
    have hd1' : (d : ℝ) + 1 ≠ 0 := by linarith
    field_simp
  have hapow : a ^ (1 + (1 : ℝ) / (d : ℝ)) = (n : ℝ) / (8 * K * β) := by
    rw [ha, ← Real.rpow_mul (by positivity), hexpo, Real.rpow_one]
  have hthr : 8 * K * β * (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) ≤ (n : ℝ) := by
    have hkpow : (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) ≤ (n : ℝ) / (8 * K * β) := by
      rw [← hapow]
      exact Real.rpow_le_rpow hkR hkle (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hkpow hAB.le
    have heq : 8 * K * β * ((n : ℝ) / (8 * K * β)) = (n : ℝ) := by field_simp
    linarith [hmul, heq.le, heq.ge]
  -- `β^{-e}n^e = (n/β)^e = B·a`.
  have hnb0 : (0 : ℝ) ≤ (n : ℝ) / β := by positivity
  have hratio : β ^ (-e) * (n : ℝ) ^ e = B * a := by
    rw [ha, hB, Real.div_rpow hn0 hAB.le, Real.mul_rpow hA.le hβpos.le, Real.rpow_neg hβpos.le]
    have h2 : (β ^ e) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hβpos e)
    have h1 : ((8 * K) ^ e) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hA e)
    field_simp
  have hxa : ((n : ℝ) / β) ^ e = B * a := by
    rw [← hratio, Real.div_rpow hn0 hβpos.le, Real.rpow_neg hβpos.le]
    field_simp
  -- The event inclusion.
  have hincl : prb (d := d) n β (fun w =>
        ((R w n).card : ℝ) < c * β ^ (-e) * (n : ℝ) ^ e)
      ≤ prb (d := d) n β
        (fun w => 8 * K * β * (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) < (sigma w k : ℝ)) := by
    refine prb_mono hd1 hβ _ _ ?_
    intro w hw
    have heq2 : B⁻¹ / (2 * (d : ℝ)) * (B * a) = a / (2 * (d : ℝ)) := by
      field_simp
    have hstep : c * (B * a) ≤ B⁻¹ / (2 * (d : ℝ)) * (B * a) :=
      mul_le_mul_of_nonneg_right hc1 (by positivity)
    have hfin : a / (2 * (d : ℝ)) ≤ (k : ℝ) / (d : ℝ) := by
      rw [div_le_div_iff₀ (by linarith) hdRpos]
      nlinarith [hkge, hdRpos]
    have hcbound : c * β ^ (-e) * (n : ℝ) ^ e ≤ (k : ℝ) / (d : ℝ) := by
      calc c * β ^ (-e) * (n : ℝ) ^ e = c * (B * a) := by rw [← hratio]; ring
        _ ≤ B⁻¹ / (2 * (d : ℝ)) * (B * a) := hstep
        _ = a / (2 * (d : ℝ)) := heq2
        _ ≤ (k : ℝ) / (d : ℝ) := hfin
    have hlt : ((R w n).card : ℝ) < (k : ℝ) / (d : ℝ) := lt_of_lt_of_le hw hcbound
    have hlt2 : (d : ℝ) * ((R w n).card : ℝ) < (k : ℝ) := by
      rw [lt_div_iff₀ hdRpos] at hlt
      linarith
    have hltN : d * (R w n).card < k := by exact_mod_cast hlt2
    have hEle : (E w n).card < k := lt_of_le_of_lt (ORRW.card_edges_le_card_range w n) hltN
    have hnot : ¬ (sigma w k ≤ n) := by
      intro hcon
      exact absurd ((sigma_le_iff w (le_refl n)).mp hcon) (by omega)
    have hgt : (n : ℝ) < (sigma w k : ℝ) := by
      have : n < sigma w k := by omega
      exact_mod_cast this
    linarith [hthr, hgt]
  -- The exponent.
  have hexpbd : c * ((n : ℝ) / β) ^ g ≤ c₀ * (k : ℝ) ^ f := by
    have hX : ((n : ℝ) / β) ^ e / (2 * B) ≤ (k : ℝ) := by
      rw [hxa, div_le_iff₀ (by linarith)]
      nlinarith [hkge, hBpos]
    have hXpow : (((n : ℝ) / β) ^ e / (2 * B)) ^ f ≤ (k : ℝ) ^ f :=
      Real.rpow_le_rpow (by positivity) hX hfpos.le
    have hXeq : (((n : ℝ) / β) ^ e / (2 * B)) ^ f = ((n : ℝ) / β) ^ g / (2 * B) ^ f := by
      rw [Real.div_rpow (Real.rpow_nonneg hnb0 e) (by linarith), ← Real.rpow_mul hnb0, hef]
    rw [hXeq] at hXpow
    have hng : (0 : ℝ) ≤ ((n : ℝ) / β) ^ g := Real.rpow_nonneg hnb0 g
    calc c * ((n : ℝ) / β) ^ g ≤ (c₀ / (2 * B) ^ f) * ((n : ℝ) / β) ^ g :=
          mul_le_mul_of_nonneg_right hc2 hng
      _ = c₀ * (((n : ℝ) / β) ^ g / (2 * B) ^ f) := by ring
      _ ≤ c₀ * (k : ℝ) ^ f := mul_le_mul_of_nonneg_left hXpow hc₀pos.le
  refine le_trans hincl (le_trans (hST β hβ k hk1 n hthr) ?_)
  exact Real.exp_le_exp.mpr (by linarith)

end ORRW.Support
