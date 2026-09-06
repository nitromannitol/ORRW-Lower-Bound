/-
Optional stopping for the supermartingale of `lem:martingale`, and the resulting
bound `E_β[σ_k ∧ N] ≤ Kβk^{1+1/d}` of Bou-Rabee--Peres, `orrw.tex`:

  "Optional stopping applied to the supermartingale of Lemma `lem:martingale` at
   the bounded stopping time `σ_k ∧ N` gives
   `E_β[σ_k ∧ N] + E_β Φ_{σ_k∧N} - E_β Γ_{σ_k∧N} ≤ 0`, that is,
   `E_β[σ_k ∧ N] ≤ E_β Γ_{σ_k∧N}`, because `Φ ≥ 0`.  Since `|E_{σ_k∧N}| ≤ k`,
   Proposition `prop:charge` bounds the right-hand side by `Kβk^{1+1/d}`."

Under ruling R-001 there is no infinite-path measure, so `E_β σ_k` is not a term
and the paper's passage to the limit by monotone convergence is not taken: what
is proved here is the family of finite-horizon bounds, one for every horizon
`N`, which is what the paper's own optional-stopping step establishes and all
that Theorem 1.1 and Proposition 6.1 use.  Nothing in this file is frozen.
-/
import ORRW.Support.SigmaTail
import ORRW.Support.RangeUpper

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW.Support

open Finset ORRW

variable {d : ℕ}

/-! ### Two elementary facts about `expect` -/

/-- `E_β` is monotone. -/
theorem expect_mono {N : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β)
    (f g : (Fin N → Dir d) → ℝ) (h : ∀ w, f w ≤ g w) :
    expect N β f ≤ expect N β g := by
  unfold expect
  exact Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (h w) (prob_pos hd hβ w).le

/-! ### Optional stopping

The paper's supermartingale is `n + Φ_n - Γ_n`.  Stopped at `ζ`, the statement
`E[ζ_N + Φ_N - Γ_N] ≤ 0` is an induction on the horizon whose step is one
application of the drift inequality against the step rule. -/

/-- The stopped supermartingale has nonpositive mean. -/
theorem expect_drift_nonpos (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β)
    (Φ Γ : ∀ m : ℕ, (Fin m → Dir d) → ℝ)
    (ζ χ : ∀ m : ℕ, (Fin m → Dir d) → ℕ)
    (hζ0 : ∀ v : Fin 0 → Dir d, ζ 0 v = 0)
    (hΦ0 : ∀ v : Fin 0 → Dir d, Φ 0 v = 0)
    (hΓ0 : ∀ v : Fin 0 → Dir d, Γ 0 v = 0)
    (hζ : ∀ (m : ℕ) (v : Fin m → Dir d) (a : Dir d),
        ζ (m + 1) (Fin.snoc v a) = ζ m v + χ m v)
    (hdrift : ∀ (m : ℕ) (v : Fin m → Dir d),
        (χ m v : ℝ) ≤ (∑ a : Dir d, stepWeight β v m a *
              ((Γ (m + 1) (Fin.snoc v a) - Γ m v) - (Φ (m + 1) (Fin.snoc v a) - Φ m v)))
            / mu β v m) (N : ℕ) :
    expect N β (fun w => (ζ N w : ℝ) + Φ N w - Γ N w) ≤ 0 := by
  induction N with
  | zero =>
      have hterm : ∀ w : Fin 0 → Dir d,
          prob β w * ((ζ 0 w : ℝ) + Φ 0 w - Γ 0 w) = 0 := by
        intro w
        rw [hζ0 w, hΦ0 w, hΓ0 w]
        norm_num
      unfold expect
      rw [Finset.sum_congr rfl fun w _ => hterm w, Finset.sum_const_zero]
  | succ m ih =>
      refine le_trans ?_ ih
      refine expect_succ_le hd hβ _ _ ?_
      intro v
      have htwpos : 0 < totalWeight β v m := totalWeight_pos hd hβ v m
      have hmu : mu β v m = totalWeight β v m := mu_eq_totalWeight β v m
      -- The one-step identity: the increments telescope against the drift term.
      have hsum : (∑ a : Dir d, stepWeight β v m a *
              ((ζ (m + 1) (Fin.snoc v a) : ℝ) + Φ (m + 1) (Fin.snoc v a)
                - Γ (m + 1) (Fin.snoc v a)))
            + (∑ a : Dir d, stepWeight β v m a *
              ((Γ (m + 1) (Fin.snoc v a) - Γ m v) - (Φ (m + 1) (Fin.snoc v a) - Φ m v)))
          = totalWeight β v m * ((ζ m v : ℝ) + (χ m v : ℝ) + Φ m v - Γ m v) := by
        rw [← Finset.sum_add_distrib, totalWeight, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hζ m v a]
        push_cast
        ring
      have hdr : (χ m v : ℝ) * totalWeight β v m
          ≤ ∑ a : Dir d, stepWeight β v m a *
              ((Γ (m + 1) (Fin.snoc v a) - Γ m v) - (Φ (m + 1) (Fin.snoc v a) - Φ m v)) := by
        have h := hdrift m v
        rw [hmu, le_div_iff₀ htwpos] at h
        exact h
      show (∑ a : Dir d, stepWeight β v m a *
              ((ζ (m + 1) (Fin.snoc v a) : ℝ) + Φ (m + 1) (Fin.snoc v a)
                - Γ (m + 1) (Fin.snoc v a))) / totalWeight β v m
          ≤ (ζ m v : ℝ) + Φ m v - Γ m v
      rw [div_le_iff₀ htwpos]
      nlinarith [hsum, hdr]

/-- Optional stopping: `E_β ζ_N ≤ b` when `Φ ≥ 0` and `Γ ≤ b`. -/
theorem expect_stopped_le (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β)
    (Φ Γ : ∀ m : ℕ, (Fin m → Dir d) → ℝ)
    (ζ χ : ∀ m : ℕ, (Fin m → Dir d) → ℕ) (b : ℝ)
    (hζ0 : ∀ v : Fin 0 → Dir d, ζ 0 v = 0)
    (hΦ0 : ∀ v : Fin 0 → Dir d, Φ 0 v = 0)
    (hΓ0 : ∀ v : Fin 0 → Dir d, Γ 0 v = 0)
    (hζ : ∀ (m : ℕ) (v : Fin m → Dir d) (a : Dir d),
        ζ (m + 1) (Fin.snoc v a) = ζ m v + χ m v)
    (hΦ : ∀ (m : ℕ) (v : Fin m → Dir d), 0 ≤ Φ m v)
    (hΓ : ∀ (m : ℕ) (v : Fin m → Dir d), Γ m v ≤ b)
    (hdrift : ∀ (m : ℕ) (v : Fin m → Dir d),
        (χ m v : ℝ) ≤ (∑ a : Dir d, stepWeight β v m a *
              ((Γ (m + 1) (Fin.snoc v a) - Γ m v) - (Φ (m + 1) (Fin.snoc v a) - Φ m v)))
            / mu β v m) (N : ℕ) :
    expect N β (fun w => (ζ N w : ℝ)) ≤ b := by
  have hsm := expect_drift_nonpos hd hβ Φ Γ ζ χ hζ0 hΦ0 hΓ0 hζ hdrift N
  have hpt : ∀ w : Fin N → Dir d,
      (ζ N w : ℝ) ≤ ((ζ N w : ℝ) + Φ N w - Γ N w) + b := by
    intro w
    have h1 := hΦ N w
    have h2 := hΓ N w
    linarith
  have hle := expect_mono hd hβ (fun w => (ζ N w : ℝ))
    (fun w => ((ζ N w : ℝ) + Φ N w - Γ N w) + b) hpt
  rw [expect_add_const hd hβ (fun w => (ζ N w : ℝ) + Φ N w - Γ N w) b] at hle
  linarith

/-! ### `eq:sigma-mean` at a finite horizon -/

/-- `E_β[σ_k ∧ N] ≤ Kβk^{1+1/d}`, the paper's `eq:sigma-mean` (`orrw.tex`)
before the passage to the limit, with `K` the constant of `prop:charge`. -/
theorem expect_min_sigma_le (hd : 2 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 1 ≤ β → ∀ k N : ℕ,
      expect (d := d) N β (fun w => ((min (sigma w k) N : ℕ) : ℝ))
        ≤ K * β * (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) := by
  have hd1 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  obtain ⟨K, hKpos, hK⟩ := ORRW.Frozen.accumulated_charge hd
  refine ⟨K, hKpos, ?_⟩
  intro β hβ k N
  have hβ0 : (0 : ℝ) ≤ β := le_trans zero_le_one hβ
  obtain ⟨b, hb⟩ : ∃ x : ℝ, x = K * β * (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) := ⟨_, rfl⟩
  -- `|E_t| ≤ k` at every stopped time.
  have hEk : ∀ (M : ℕ) (v : Fin M → Dir d), (E v (min (sigma v k) M)).card ≤ k :=
    fun M v => card_E_le_of_le_sigma v (min_le_right _ _) (min_le_left _ _)
  have hζ0 : ∀ v : Fin 0 → Dir d, min (sigma v k) 0 = 0 := fun v => Nat.min_zero _
  have hζ : ∀ (M : ℕ) (v : Fin M → Dir d) (a : Dir d),
      min (sigma (Fin.snoc v a) k) (M + 1)
        = min (sigma v k) M + (if sigma v k ≤ M then 0 else 1) := by
    intro M v a
    by_cases hcase : sigma v k ≤ M
    · rw [if_pos hcase, sigma_snoc_of_le v a hcase]; omega
    · push_neg at hcase
      have := sigma_snoc_of_lt v a hcase
      rw [if_neg (by omega)]
      omega
  have hΦ0 : ∀ v : Fin 0 → Dir d, Phi v (min (sigma v k) 0) = 0 := by
    intro v
    rw [Nat.min_zero]
    show 2 * (d : ℝ) * u (S v 0) (pos v 0) = 0
    rw [S_zero hd1 v, u_eq_zero_of_notMem _ (Finset.notMem_empty _)]
    ring
  have hΓ0 : ∀ v : Fin 0 → Dir d, Gamma β v (min (sigma v k) 0) = 0 := by
    intro v; rw [Nat.min_zero]; rfl
  have hΦnn : ∀ (M : ℕ) (v : Fin M → Dir d), 0 ≤ Phi v (min (sigma v k) M) :=
    fun M v => Phi_nonneg hd1 v _
  have hΓbd : ∀ (M : ℕ) (v : Fin M → Dir d), Gamma β v (min (sigma v k) M) ≤ b := by
    intro M v
    have h1 := hK β hβ M v (min (sigma v k) M)
    have h2 : (((E v (min (sigma v k) M)).card : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hEk M v
    have h3 : (((E v (min (sigma v k) M)).card : ℝ)) ^ (1 + (1 : ℝ) / (d : ℝ))
        ≤ (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) :=
      Real.rpow_le_rpow (by positivity) h2 (by positivity)
    rw [hb]
    nlinarith [h1, h3, hKpos, hβ0, mul_nonneg hKpos.le hβ0]
  have hdrift : ∀ (M : ℕ) (v : Fin M → Dir d),
      ((if sigma v k ≤ M then 0 else 1 : ℕ) : ℝ)
        ≤ (∑ a : Dir d, stepWeight β v M a *
              ((Gamma β (Fin.snoc v a) (min (sigma (Fin.snoc v a) k) (M + 1))
                  - Gamma β v (min (sigma v k) M))
                - (Phi (Fin.snoc v a) (min (sigma (Fin.snoc v a) k) (M + 1))
                  - Phi v (min (sigma v k) M)))) / mu β v M := by
    intro M v
    by_cases hcase : sigma v k ≤ M
    · rw [if_pos hcase]
      have hzero : ∀ a : Dir d, stepWeight β v M a *
            ((Gamma β (Fin.snoc v a) (min (sigma (Fin.snoc v a) k) (M + 1))
                - Gamma β v (min (sigma v k) M))
              - (Phi (Fin.snoc v a) (min (sigma (Fin.snoc v a) k) (M + 1))
                - Phi v (min (sigma v k) M))) = 0 := by
        intro a
        have hs : sigma (Fin.snoc v a) k = sigma v k := sigma_snoc_of_le v a hcase
        rw [show min (sigma (Fin.snoc v a) k) (M + 1) = sigma v k by rw [hs]; omega,
          show min (sigma v k) M = sigma v k by omega,
          Gamma_snoc hd1 β v a _ hcase, Phi_snoc hd1 v a hcase]
        ring
      rw [Finset.sum_congr rfl (fun a _ => hzero a)]
      simp
    · push_neg at hcase
      rw [if_neg (by omega)]
      have hcongr : ∀ a : Dir d, stepWeight β v M a *
            ((Gamma β (Fin.snoc v a) (min (sigma (Fin.snoc v a) k) (M + 1))
                - Gamma β v (min (sigma v k) M))
              - (Phi (Fin.snoc v a) (min (sigma (Fin.snoc v a) k) (M + 1))
                - Phi v (min (sigma v k) M)))
          = stepWeight β v M a *
            ((Gamma β (Fin.snoc v a) (M + 1) - Gamma β (Fin.snoc v a) M)
              - (Phi (Fin.snoc v a) (M + 1) - Phi (Fin.snoc v a) M)) := by
        intro a
        have hs := sigma_snoc_of_lt v a hcase
        rw [show min (sigma (Fin.snoc v a) k) (M + 1) = M + 1 by omega,
          show min (sigma v k) M = M by omega,
          Gamma_snoc hd1 β v a M (le_refl M), Phi_snoc hd1 v a (le_refl M)]
      rw [Finset.sum_congr rfl (fun a _ => hcongr a), Nat.cast_one]
      exact ORRW.Frozen.supermartingale_drift hd1 hβ M v
  have := expect_stopped_le hd1 hβ
    (fun M v => Phi v (min (sigma v k) M))
    (fun M v => Gamma β v (min (sigma v k) M))
    (fun M v => min (sigma v k) M)
    (fun M v => if sigma v k ≤ M then 0 else 1)
    b hζ0 hΦ0 hΓ0 hζ hΦnn hΓbd hdrift N
  rw [← hb]
  exact this

end ORRW.Support
