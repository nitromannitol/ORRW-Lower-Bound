/-
Choosing the truncation `R`, `orrw.tex`.

The three terms of `eq:optimize` are `h R^{-d/2}`, `H_d(R)` and `(β-1)√R`; the
first and third balance at `R = ⌈(h/(β-1))^{2/(d+1)}⌉`, where both equal a
constant multiple of `(β-1)^{d/(d+1)} h^{1/(d+1)}`.  The paper's three regimes
(`β-1` above `h`, below `h^{-1/2}`, and in between) are the three cases below.

The statement is packaged so that the probabilistic part of Theorem 8.2 supplies
only the two bounds it proves -- the trivial bound `X ≤ h` and the bound for
every `R ≥ 1` -- and this file supplies the constant.
-/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

private lemma one_le_log_add_two (h : ℕ) (hh : 1 ≤ h) : (1:ℝ) ≤ Real.log ((h:ℝ) + 2) := by
  have hh1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hpos : (0:ℝ) < (h:ℝ) + 2 := by linarith
  refine (Real.le_log_iff_exp_le hpos).2 ?_
  have := Real.exp_one_lt_d9
  linarith

private lemma rpow_mul_rpow_of_add_eq_one {x a b : ℝ} (hx : 0 < x) (hab : a + b = 1) :
    x ^ a * x ^ b = x := by
  rw [← Real.rpow_add hx, hab, Real.rpow_one]

private lemma optimize_key_pow {dd t x : ℝ} (hdd : 0 ≤ dd) (ht : 0 < t) (hx : 0 < x) :
    x * ((x / t) ^ (2 / (dd + 1))) ^ (-dd / 2)
      = t ^ (dd / (dd + 1)) * x ^ (1 / (dd + 1)) := by
  have he : (dd : ℝ) + 1 ≠ 0 := by positivity
  have hu : (0:ℝ) < x / t := div_pos hx ht
  have hmul : 2 / (dd + 1) * (-dd / 2) = -(dd / (dd + 1)) := by
    field_simp
  rw [← Real.rpow_mul hu.le, hmul, Real.rpow_neg hu.le,
    Real.div_rpow hx.le ht.le, inv_div]
  have hexp : (1:ℝ) - dd / (dd + 1) = 1 / (dd + 1) := by
    field_simp
    ring
  have hsub : x ^ (1 / (dd + 1)) = x / x ^ (dd / (dd + 1)) := by
    rw [← hexp, Real.rpow_sub hx, Real.rpow_one]
  rw [hsub]
  ring

private lemma optimize_key_sqrt {dd t x : ℝ} (hdd : 0 ≤ dd) (ht : 0 < t) (hx : 0 < x) :
    t * Real.sqrt ((x / t) ^ (2 / (dd + 1)))
      = t ^ (dd / (dd + 1)) * x ^ (1 / (dd + 1)) := by
  have he : (dd : ℝ) + 1 ≠ 0 := by positivity
  have hu : (0:ℝ) < x / t := div_pos hx ht
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hu.le]
  have hmul : 2 / (dd + 1) * (1 / 2) = 1 / (dd + 1) := by field_simp
  rw [hmul, Real.div_rpow hx.le ht.le]
  have hexp : (1:ℝ) - 1 / (dd + 1) = dd / (dd + 1) := by
    field_simp
    ring
  have hsub : t ^ (dd / (dd + 1)) = t / t ^ (1 / (dd + 1)) := by
    rw [← hexp, Real.rpow_sub ht, Real.rpow_one]
  rw [hsub]
  ring

/-- The optimization of `orrw.tex`. -/
theorem optimize_R (d : ℕ) (hd : 2 ≤ d) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ h : ℕ, 1 ≤ h → ∀ X : ℝ,
      X ≤ (h : ℝ) →
      (∀ R : ℕ, 1 ≤ R → X ≤ 1 + A * ((h : ℝ) * (R : ℝ) ^ (-(d : ℝ) / 2)
          + (if d = 2 then Real.log ((R : ℝ) + 1) else 1) + t * Real.sqrt (R : ℝ))) →
      X ≤ C * ((if d = 2 then Real.log ((h : ℝ) + 2) else 1)
          + t ^ ((d : ℝ) / ((d : ℝ) + 1)) * (h : ℝ) ^ (1 / ((d : ℝ) + 1))) := by
  refine ⟨1 + 3 * A, ?_⟩
  intro t ht h hh X hXh hbd
  have hdR : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have he : (0:ℝ) < (d:ℝ) + 1 := by linarith
  have hne : ((d:ℝ) + 1) ≠ 0 := ne_of_gt he
  have hh1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hh0 : (0:ℝ) < (h:ℝ) := by linarith
  have hexp1 : (d:ℝ) / ((d:ℝ) + 1) + 1 / ((d:ℝ) + 1) = 1 := by
    field_simp
  set H : ℝ := (if d = 2 then Real.log ((h:ℝ) + 2) else 1) with hHdef
  set S : ℝ := t ^ ((d:ℝ) / ((d:ℝ) + 1)) * (h:ℝ) ^ (1 / ((d:ℝ) + 1)) with hSdef
  clear_value H S
  have hH1 : (1:ℝ) ≤ H := by
    rw [hHdef]
    split_ifs with hc
    · exact one_le_log_add_two h hh
    · exact le_refl 1
  have hS0 : (0:ℝ) ≤ S := by
    rw [hSdef]
    exact mul_nonneg (Real.rpow_nonneg ht _) (Real.rpow_nonneg hh0.le _)
  rcases lt_or_ge (h:ℝ) t with hcase | hcase
  · -- Case A: `h < t`, the trivial bound already suffices.
    have hmono : (h:ℝ) ^ ((d:ℝ) / ((d:ℝ) + 1)) ≤ t ^ ((d:ℝ) / ((d:ℝ) + 1)) :=
      Real.rpow_le_rpow hh0.le hcase.le (by positivity)
    have hSh : (h:ℝ) ≤ S := by
      rw [hSdef]
      calc (h:ℝ) = (h:ℝ) ^ ((d:ℝ) / ((d:ℝ) + 1)) * (h:ℝ) ^ (1 / ((d:ℝ) + 1)) :=
            (rpow_mul_rpow_of_add_eq_one hh0 hexp1).symm
        _ ≤ t ^ ((d:ℝ) / ((d:ℝ) + 1)) * (h:ℝ) ^ (1 / ((d:ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hh0.le _)
    nlinarith [mul_nonneg hA (le_trans zero_le_one hH1), mul_nonneg hA hS0]
  rcases le_or_gt t ((h:ℝ) ^ (-(1:ℝ) / 2)) with hc2 | hc2
  · -- Case B: `t√h ≤ 1`, take `R = h`.
    have key := hbd h hh
    have b1 : (h:ℝ) * (h:ℝ) ^ (-(d:ℝ) / 2) ≤ 1 := by
      have e1 : (h:ℝ) * (h:ℝ) ^ (-(d:ℝ) / 2) = (h:ℝ) ^ (1 + -(d:ℝ) / 2) := by
        rw [Real.rpow_add hh0, Real.rpow_one]
      rw [e1]
      calc (h:ℝ) ^ (1 + -(d:ℝ) / 2) ≤ (h:ℝ) ^ (0:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hh1 (by linarith)
        _ = 1 := Real.rpow_zero _
    have b2 : (if d = 2 then Real.log ((h:ℝ) + 1) else 1) ≤ H := by
      rw [hHdef]
      split_ifs with hc
      · exact Real.log_le_log (by linarith) (by linarith)
      · exact le_refl 1
    have b3 : t * Real.sqrt (h:ℝ) ≤ 1 := by
      rw [Real.sqrt_eq_rpow]
      calc t * (h:ℝ) ^ ((1:ℝ) / 2) ≤ (h:ℝ) ^ (-(1:ℝ) / 2) * (h:ℝ) ^ ((1:ℝ) / 2) :=
            mul_le_mul_of_nonneg_right hc2 (Real.rpow_nonneg hh0.le _)
        _ = (h:ℝ) ^ (0:ℝ) := by rw [← Real.rpow_add hh0]; norm_num
        _ = 1 := Real.rpow_zero _
    have hstep : A * ((h:ℝ) * (h:ℝ) ^ (-(d:ℝ) / 2)
        + (if d = 2 then Real.log ((h:ℝ) + 1) else 1) + t * Real.sqrt (h:ℝ))
        ≤ A * (1 + H + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hA
    nlinarith [mul_nonneg hA (sub_nonneg.2 hH1), mul_nonneg hA hS0]
  · -- Case C: `h^{-1/2} < t ≤ h`, balance the first and third terms.
    have ht0 : (0:ℝ) < t := lt_trans (Real.rpow_pos_of_pos hh0 _) hc2
    obtain ⟨rho, hrho⟩ : ∃ r : ℝ, r = ((h:ℝ) / t) ^ (2 / ((d:ℝ) + 1)) := ⟨_, rfl⟩
    have hrho0 : (0:ℝ) < rho := by
      rw [hrho]; exact Real.rpow_pos_of_pos (div_pos hh0 ht0) _
    have hR1 : 1 ≤ ⌈rho⌉₊ := Nat.ceil_pos.2 hrho0
    have hleR : rho ≤ (⌈rho⌉₊ : ℝ) := Nat.le_ceil rho
    have hRlt : ((⌈rho⌉₊ : ℕ) : ℝ) < rho + 1 := Nat.ceil_lt_add_one hrho0.le
    have hRpos : (0:ℝ) < ((⌈rho⌉₊ : ℕ) : ℝ) := lt_of_lt_of_le hrho0 hleR
    have htS : t ≤ S := by
      rw [hSdef]
      calc t = t ^ ((d:ℝ) / ((d:ℝ) + 1)) * t ^ (1 / ((d:ℝ) + 1)) :=
            (rpow_mul_rpow_of_add_eq_one ht0 hexp1).symm
        _ ≤ t ^ ((d:ℝ) / ((d:ℝ) + 1)) * (h:ℝ) ^ (1 / ((d:ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht0.le hcase (by positivity))
              (Real.rpow_nonneg ht0.le _)
    have c1 : (h:ℝ) * ((⌈rho⌉₊ : ℕ) : ℝ) ^ (-(d:ℝ) / 2) ≤ S := by
      have hmono : rho ^ ((d:ℝ) / 2) ≤ (((⌈rho⌉₊ : ℕ) : ℝ)) ^ ((d:ℝ) / 2) :=
        Real.rpow_le_rpow hrho0.le hleR (by positivity)
      have hneg : -(d:ℝ) / 2 = -((d:ℝ) / 2) := by ring
      have hinv : (((⌈rho⌉₊ : ℕ) : ℝ)) ^ (-(d:ℝ) / 2) ≤ rho ^ (-(d:ℝ) / 2) := by
        rw [hneg, Real.rpow_neg hRpos.le, Real.rpow_neg hrho0.le]
        exact (inv_le_inv₀ (Real.rpow_pos_of_pos hRpos _)
          (Real.rpow_pos_of_pos hrho0 _)).2 hmono
      calc (h:ℝ) * (((⌈rho⌉₊ : ℕ) : ℝ)) ^ (-(d:ℝ) / 2)
          ≤ (h:ℝ) * rho ^ (-(d:ℝ) / 2) := mul_le_mul_of_nonneg_left hinv hh0.le
        _ = S := by
            rw [hrho, hSdef]
            exact optimize_key_pow (by positivity) ht0 hh0
    have hrhoh : rho ≤ (h:ℝ) := by
      have hth : (h:ℝ) / t ≤ (h:ℝ) ^ ((3:ℝ) / 2) := by
        rw [div_le_iff₀ ht0]
        have e1 : (h:ℝ) ^ (-(1:ℝ) / 2) * (h:ℝ) ^ ((3:ℝ) / 2) = (h:ℝ) := by
          rw [← Real.rpow_add hh0]; norm_num
        nlinarith [mul_lt_mul_of_pos_left hc2 (Real.rpow_pos_of_pos hh0 ((3:ℝ) / 2))]
      have h1 : ((h:ℝ) / t) ^ (2 / ((d:ℝ) + 1))
          ≤ ((h:ℝ) ^ ((3:ℝ) / 2)) ^ (2 / ((d:ℝ) + 1)) :=
        Real.rpow_le_rpow (div_pos hh0 ht0).le hth (by positivity)
      have h2 : ((h:ℝ) ^ ((3:ℝ) / 2)) ^ (2 / ((d:ℝ) + 1))
          = (h:ℝ) ^ ((3:ℝ) / ((d:ℝ) + 1)) := by
        rw [← Real.rpow_mul hh0.le]
        congr 1
        field_simp
      have h3 : (h:ℝ) ^ ((3:ℝ) / ((d:ℝ) + 1)) ≤ (h:ℝ) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hh1 (by rw [div_le_one he]; linarith)
      rw [Real.rpow_one] at h3
      rw [hrho]
      exact le_trans h1 (le_trans (le_of_eq h2) h3)
    have c2 : (if d = 2 then Real.log (((⌈rho⌉₊ : ℕ) : ℝ) + 1) else 1) ≤ H := by
      rw [hHdef]
      split_ifs with hc
      · exact Real.log_le_log (by positivity) (by linarith)
      · exact le_refl 1
    have c3 : t * Real.sqrt (((⌈rho⌉₊ : ℕ) : ℝ)) ≤ 2 * S := by
      have hsq : Real.sqrt (((⌈rho⌉₊ : ℕ) : ℝ)) ≤ Real.sqrt rho + 1 := by
        have h1 : (((⌈rho⌉₊ : ℕ) : ℝ)) ≤ (Real.sqrt rho + 1) ^ 2 := by
          nlinarith [Real.sqrt_nonneg rho, Real.sq_sqrt hrho0.le, hRlt]
        calc Real.sqrt (((⌈rho⌉₊ : ℕ) : ℝ)) ≤ Real.sqrt ((Real.sqrt rho + 1) ^ 2) :=
              Real.sqrt_le_sqrt h1
          _ = Real.sqrt rho + 1 := Real.sqrt_sq (by positivity)
      have hts : t * Real.sqrt rho = S := by
        rw [hrho, hSdef]
        exact optimize_key_sqrt (by positivity) ht0 hh0
      nlinarith [mul_le_mul_of_nonneg_left hsq ht0.le]
    have key := hbd ⌈rho⌉₊ hR1
    have hstep : A * ((h:ℝ) * ((⌈rho⌉₊ : ℕ) : ℝ) ^ (-(d:ℝ) / 2)
        + (if d = 2 then Real.log (((⌈rho⌉₊ : ℕ) : ℝ) + 1) else 1)
        + t * Real.sqrt (((⌈rho⌉₊ : ℕ) : ℝ)))
        ≤ A * (S + H + 2 * S) :=
      mul_le_mul_of_nonneg_left (by linarith) hA
    nlinarith [mul_nonneg hA hS0, mul_nonneg hA (le_trans zero_le_one hH1)]

end ORRW
