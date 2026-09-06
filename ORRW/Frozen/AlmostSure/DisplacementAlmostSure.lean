/-
Frozen statement of the paper's almost-sure displacement bound.

`orrw.tex`, the last display of `prop:displacement`: "Moreover,
`P_beta`-almost surely, `liminf_{n -> infty} Lambda_n n^{-1/(d+1)} >=
c beta^{-1/(d+1)}`."

This is the second and last of the two claims that ruling R-001 could not
express.  The paper derives it from `eq:range-box` and the almost-sure
consequence of `thm:whp`; so does this proof, from `ORRW.Frozen.range_ae` and
`ORRW.Support.card_range_le_box`.

Modelling decisions.

* Ruling A-003 (`liminf` as an eventual bound), as in `ae-range`.
* Ruling A-004 (`Lambda_n`).  The paper's maximal displacement is rendered as
  `(range (n+1)).sup' _ (fun k => ‖pos w k‖)`, the same expression the frozen
  `prop-displacement` uses, evaluated along `ORRW.ofPath n`.
-/
import ORRW.Frozen.AlmostSure.RangeAlmostSure
import ORRW.Support.RangeBox

open MeasureTheory ProbabilityTheory Finset Preorder Filter Real Asymptotics
open scoped ENNReal

open ORRW in
set_option maxHeartbeats 2000000 in
-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.displacement_ae {d : ℕ} [hd0 : Fact (0 < d)] (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 1 ≤ β),
      ∀ᵐ ω ∂(@ORRW.pathMeasure d hd0 β ⟨hβ⟩), ∀ᶠ n : ℕ in atTop,
        c * β ^ (-((1 : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1))
          ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              (fun k => ‖ORRW.pos (ORRW.ofPath n ω) k‖)
-- FROZEN-STATEMENT-END
:= by
  have hdpos : (0 : ℝ) < (d : ℝ) := by positivity
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  obtain ⟨c, hc, hae0⟩ := ORRW.Frozen.range_ae (d := d) hd
  refine ⟨c ^ ((1 : ℝ) / (d : ℝ)) / 4, by positivity, ?_⟩
  intro β hβ
  haveI : Fact (1 ≤ β) := ⟨hβ⟩
  have hae := hae0 β hβ
  set A : ℝ := c ^ ((1 : ℝ) / (d : ℝ)) * β ^ (-((1 : ℝ) / ((d : ℝ) + 1))) with hA
  have hApos : 0 < A := by
    have h1 : (0:ℝ) < c ^ ((1:ℝ)/(d:ℝ)) := Real.rpow_pos_of_pos hc _
    have h2 : (0:ℝ) < β ^ (-((1:ℝ)/((d:ℝ)+1))) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  -- eventually the additive constant 3 is negligible
  have hgrow : ∀ᶠ n : ℕ in atTop, (6 : ℝ) ≤ A * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1)) := by
    have ht : Tendsto (fun n : ℕ => A * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1))) atTop atTop := by
      refine Tendsto.const_mul_atTop hApos ?_
      exact (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
    exact ht.eventually_ge_atTop 6
  filter_upwards [hae] with ω hω
  filter_upwards [hω, hgrow] with n hn hbig
  set L : ℝ := (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k => ‖pos (ofPath n ω) k‖) with hL
  have hLnn : 0 ≤ L := by
    refine le_trans (norm_nonneg (pos (ofPath n ω) 0)) ?_
    exact Finset.le_sup' (f := fun k => ‖pos (ofPath n ω) k‖) (by simp)
  -- the range sits in a box of radius ceil L
  have hbox : ((R (ofPath n ω) n).card : ℝ) ≤ (2 * L + 3) ^ (d : ℕ) := by
    have hr : ∀ j ≤ n, ‖pos (ofPath n ω) j‖ ≤ ((⌈L⌉₊ : ℕ) : ℝ) := by
      intro j hj
      refine le_trans ?_ (Nat.le_ceil L)
      exact Finset.le_sup' (f := fun k => ‖pos (ofPath n ω) k‖) (by simp [Nat.lt_succ_iff, hj])
    have := ORRW.Support.card_range_le_box (ofPath n ω) n ⌈L⌉₊ hr
    have hcast : ((R (ofPath n ω) n).card : ℝ) ≤ (((2 * ⌈L⌉₊ + 1) ^ d : ℕ) : ℝ) := by
      exact_mod_cast this
    refine le_trans hcast ?_
    have hceil : ((⌈L⌉₊ : ℕ) : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one hLnn).le
    have hbase : ((2 * ⌈L⌉₊ + 1 : ℕ) : ℝ) ≤ 2 * L + 3 := by push_cast; linarith
    have : (((2 * ⌈L⌉₊ + 1) ^ d : ℕ) : ℝ) = (((2 * ⌈L⌉₊ + 1 : ℕ) : ℝ)) ^ d := by push_cast; ring
    rw [this]
    exact pow_le_pow_left₀ (by positivity) hbase d
  -- take d-th roots
  have hLb : (0:ℝ) ≤ 2 * L + 3 := by linarith
  have hchain : c * β ^ (-((d:ℝ)/((d:ℝ)+1))) * (n:ℝ) ^ ((d:ℝ)/((d:ℝ)+1))
      ≤ (2 * L + 3) ^ (d:ℕ) := le_trans hn hbox
  have hroot : A * (n:ℝ) ^ ((1:ℝ)/((d:ℝ)+1)) ≤ 2 * L + 3 := by
    have hnn : (0:ℝ) ≤ c * β ^ (-((d:ℝ)/((d:ℝ)+1))) * (n:ℝ) ^ ((d:ℝ)/((d:ℝ)+1)) := by
      have h1 : (0:ℝ) < β ^ (-((d:ℝ)/((d:ℝ)+1))) := Real.rpow_pos_of_pos (by linarith) _
      positivity
    have hmono := Real.rpow_le_rpow hnn hchain (by positivity : (0:ℝ) ≤ 1/(d:ℝ))
    have hR : ((2 * L + 3) ^ (d:ℕ)) ^ ((1:ℝ)/(d:ℝ)) = 2 * L + 3 := by
      rw [← Real.rpow_natCast (2 * L + 3) d, ← Real.rpow_mul hLb]
      rw [mul_one_div, div_self (ne_of_gt hdpos), Real.rpow_one]
    have hL' : (c * β ^ (-((d:ℝ)/((d:ℝ)+1))) * (n:ℝ) ^ ((d:ℝ)/((d:ℝ)+1))) ^ ((1:ℝ)/(d:ℝ))
        = A * (n:ℝ) ^ ((1:ℝ)/((d:ℝ)+1)) := by
      have hbpos : (0:ℝ) < β := by linarith
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _),
        Real.mul_rpow hc.le (Real.rpow_nonneg hbpos.le _),
        ← Real.rpow_mul hbpos.le, ← Real.rpow_mul (Nat.cast_nonneg n), hA]
      have he1 : -((d:ℝ)/((d:ℝ)+1)) * (1/(d:ℝ)) = -((1:ℝ)/((d:ℝ)+1)) := by
        field_simp
      have he2 : (d:ℝ)/((d:ℝ)+1) * (1/(d:ℝ)) = (1:ℝ)/((d:ℝ)+1) := by
        field_simp
      rw [he1, he2]
    rwa [hR, hL'] at hmono
  -- and absorb the additive constant
  have : c ^ ((1:ℝ)/(d:ℝ)) / 4 * β ^ (-((1:ℝ)/((d:ℝ)+1))) * (n:ℝ) ^ ((1:ℝ)/((d:ℝ)+1))
      = A * (n:ℝ) ^ ((1:ℝ)/((d:ℝ)+1)) / 4 := by rw [hA]; ring
  rw [this]
  linarith

