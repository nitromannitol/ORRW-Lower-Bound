/-
Supporting lemmas for Proposition 5.2 of Bou-Rabee--Peres (`prop:tail`,
`orrw.tex`): the tail of `σ_k`.

Nothing here is frozen.  The parts are

* the prefix invariance of the accumulated charge, and the behaviour of `σ_k`
  under extending the word by one letter, which is what makes the stopped
  processes `Φ_{n∧σ_k}` and `Γ_{n∧σ_k}` a legitimate input to `lem:exp`;

* the bounds `Φ_n ≤ C₁k^{2/d}` and `0 ≤ γ_n ≤ C₁βk^{2/d}` for `n ≤ σ_k` of
  `orrw.tex`, which come from `|S_n| ≤ |E_n| + 1 ≤ k + 1` and
  `lem:max-exit`;

* monotonicity of `ℙ_β` in the event.
-/
import ORRW.Support.Charge
import ORRW.Support.Return
import ORRW.Frozen.Insertion.ExitTimeBounds
import ORRW.Frozen.Potential.AccumulatedCharge
import ORRW.Frozen.Potential.Supermartingale
import ORRW.Frozen.Tail.TimeVersusCharge

namespace ORRW.Support

open Finset ORRW

variable {d m n : ℕ}

/-! ### Prefix invariance -/

/-- States how the exit-time functional η behaves when a single letter is appended to a word, the one-step extension property underlying the stopped processes used in the tail bound for σ_k. -/
lemma eta_snoc (v : Fin m → Dir d) (a : Dir d) {t : ℕ} (ht : t ≤ m) :
    eta (Fin.snoc v a) t = eta v t := by
  unfold eta
  rw [E_snoc v a ht, E_snoc v a (by omega : t - 1 ≤ m)]

/-- The accumulated charge up to time `t ≤ m` does not see the `(m+1)`st letter. -/
lemma Gamma_snoc (hd : 0 < d) (β : ℝ) (v : Fin m → Dir d) (a : Dir d) :
    ∀ t : ℕ, t ≤ m → Gamma β (Fin.snoc v a) t = Gamma β v t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro ht
      have h1 : Gamma β (Fin.snoc v a) (t + 1)
          = Gamma β (Fin.snoc v a) t
            + eta (Fin.snoc v a) (t + 1)
              * (gamma β (Fin.snoc v a) t + Phi (Fin.snoc v a) (t + 1)) := rfl
      have h2 : Gamma β v (t + 1)
          = Gamma β v t + eta v (t + 1) * (gamma β v t + Phi v (t + 1)) := rfl
      rw [h1, h2, ih (by omega), eta_snoc v a ht, gamma_snoc hd β v a (by omega),
        Phi_snoc hd v a ht]

/-! ### `σ_k` under extension of the word -/

/-- Extends the word by one letter and shows the stopping time σ_k either stays put or advances to the new length, the invariance needed to feed the stopped processes into the exponential lemma. -/
lemma sigma_snoc_of_le (v : Fin m → Dir d) (a : Dir d) {k : ℕ} (hk : sigma v k ≤ m) :
    sigma (Fin.snoc v a) k = sigma v k := by
  have hEm : E (Fin.snoc v a) m = E v m := E_snoc v a (le_refl m)
  have hkm : k ≤ (E v m).card := (sigma_le_iff v (le_refl m)).mp hk
  have hle1 : sigma (Fin.snoc v a) k ≤ sigma v k := by
    refine (sigma_le_iff (Fin.snoc v a) (by omega : sigma v k ≤ m + 1)).mpr ?_
    rw [E_snoc v a hk]
    exact (sigma_le_iff v hk).mp (le_refl _)
  have hle2 : sigma v k ≤ sigma (Fin.snoc v a) k := by
    have hsm : sigma (Fin.snoc v a) k ≤ m := le_trans hle1 hk
    refine (sigma_le_iff v hsm).mpr ?_
    rw [← E_snoc v a hsm]
    exact (sigma_le_iff (Fin.snoc v a) (by omega)).mp (le_refl _)
  omega

/-- Appending one letter to a word whose accumulated charge has not yet reached the level k leaves the stopping time σ_k unchanged, so the stopped processes are stable under extending the walk by a single step. -/
lemma sigma_snoc_of_lt (v : Fin m → Dir d) (a : Dir d) {k : ℕ} (hk : m < sigma v k) :
    m + 1 ≤ sigma (Fin.snoc v a) k := by
  by_contra hc
  push_neg at hc
  have h1 : k ≤ (E (Fin.snoc v a) m).card :=
    (sigma_le_iff (Fin.snoc v a) (by omega : m ≤ m + 1)).mp (by omega)
  rw [E_snoc v a (le_refl m)] at h1
  have := (sigma_le_iff v (le_refl m)).mpr h1
  omega

/-! ### `|E_t| ≤ k` up to the `k`th discovery -/

/-- Used to bound the range of a walk by k whenever the exit time σ_k dominates the time t, feeding the estimate |S_n| ≤ |E_n| + 1 into the potential and charge bounds for Proposition 5.2. -/
lemma card_E_le_of_le_sigma (w : Fin n → Dir d) {k t : ℕ} (ht : t ≤ n)
    (hts : t ≤ sigma w k) : (E w t).card ≤ k := by
  rcases eq_or_lt_of_le hts with heq | hlt
  · have hsn : sigma w k ≤ n := by omega
    have hfin : k ≤ (E w n).card := (sigma_le_iff w (le_refl n)).mp hsn
    rw [heq, card_E_sigma w hfin]
  · exact le_of_lt (card_E_lt_of_lt_sigma w hlt ht)

/-! ### Monotonicity of the probability in the event -/

/-- Monotonicity of the weighted path probability in the underlying event, used to pass tail estimates from the stopped processes to the events appearing in Proposition 5.2. -/
lemma prb_mono (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) {N : ℕ}
    (P Q : (Fin N → Dir d) → Prop) (hPQ : ∀ w, P w → Q w) :
    prb N β P ≤ prb N β Q := by
  classical
  unfold prb
  refine Finset.sum_le_sum fun w _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (prob_pos hd hβ w).le
  by_cases h : P w
  · rw [if_pos h, if_pos (hPQ w h)]
  · rw [if_neg h]
    split <;> norm_num

/-! ### Elementary positivity -/

/-- The accumulated charge and its exponential weight are nonnegative along a walk, the sign facts needed when bounding the stopped processes before σ_k. -/
lemma Phi_nonneg (hd : 0 < d) (w : Fin n → Dir d) (t : ℕ) : 0 ≤ Phi w t :=
  mul_nonneg (by positivity) (u_nonneg hd _ _)

/-- The accumulated charge γ is never negative, a basic bound used alongside its upper estimate when controlling the stopped process before the exit time. -/
lemma gamma_nonneg (hd : 0 < d) {β : ℝ} (hβ0 : 0 ≤ β) (w : Fin n → Dir d) (t : ℕ) :
    0 ≤ gamma β w t := by
  unfold gamma
  split
  · exact le_refl 0
  · have h1 : (1 : ℝ) ≤ ORRW.h (S w t) (pos w t) := one_le_h hd _ _
    have h2 : (0 : ℝ) ≤ 2 * (d : ℝ) * β := mul_nonneg (by positivity) hβ0
    exact mul_nonneg h2 (by linarith)

/-- The potential accumulated along a walk is always nonnegative, a basic sanity bound used when applying the exponential estimate to the stopped processes. -/
lemma eta_nonneg (w : Fin n → Dir d) (t : ℕ) : 0 ≤ eta w t := by
  unfold eta; split <;> norm_num

/-- The potential accumulated along a walk never exceeds one, the basic boundedness fact underlying the estimates on Φ and γ before the exit time. -/
lemma eta_le_one (w : Fin n → Dir d) (t : ℕ) : eta w t ≤ 1 := by
  unfold eta; split <;> norm_num

/-! ### The bounds of `orrw.tex` -/

/-- Bounds the range of a walk prefix by the time parameter, supplying the |S_t| ≤ t + 1 estimate used to control the potential and charge before the exit time. -/
lemma card_S_le (w : Fin n → Dir d) {t : ℕ} (ht : t ≤ n) :
    (S w t).card ≤ (E w t).card + 1 :=
  le_trans (Finset.card_le_card (S_subset_R w t)) (card_R_le_card_E w ht)

/-- A small numeric bridge ensuring the accumulated charge lower bound is at least one, since the range size k is positive and the potential y is nonnegative. -/
lemma one_le_rpow_cast {k : ℕ} (hk : 1 ≤ k) {y : ℝ} (hy : 0 ≤ y) : (1 : ℝ) ≤ (k : ℝ) ^ y := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hkR hy
  rwa [Real.one_rpow] at h

/-- A small numerical bound used to absorb the factor 2^{2/d} into the constants when d is at least 2. -/
lemma two_rpow_two_div_le (hd : 2 ≤ d) : (2 : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤ 2 := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hle : (2 : ℝ) / (d : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hle
  rwa [Real.rpow_one] at h

/-- The exit-time bound at a saturated set met before the `k`th discovery.
`|S_t| ≤ |E_t| + 1 ≤ k + 1 ≤ 2k`, so `lem:max-exit` gives `C(2k)^{2/d}`. -/
lemma card_S_rpow_le (hd : 2 ≤ d) (w : Fin n → Dir d) {t k : ℕ} (ht : t ≤ n)
    (hk1 : 1 ≤ k) (hE : (E w t).card ≤ k) :
    (((S w t).card : ℝ)) ^ ((2 : ℝ) / (d : ℝ)) ≤ 2 * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
  have hexp2 : (0 : ℝ) ≤ (2 : ℝ) / (d : ℝ) := by positivity
  have hcard : (((S w t).card : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
    have h : (S w t).card ≤ 2 * k := by have := card_S_le w ht; omega
    exact_mod_cast h
  have hpow : (((S w t).card : ℝ)) ^ ((2 : ℝ) / (d : ℝ))
      ≤ (2 * (k : ℝ)) ^ ((2 : ℝ) / (d : ℝ)) :=
    Real.rpow_le_rpow (by positivity) hcard hexp2
  have hsplit : (2 * (k : ℝ)) ^ ((2 : ℝ) / (d : ℝ))
      = (2 : ℝ) ^ ((2 : ℝ) / (d : ℝ)) * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) :=
    Real.mul_rpow (by norm_num) (by positivity)
  have hkp0 : (0 : ℝ) ≤ (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := Real.rpow_nonneg (by positivity) _
  have h2 := two_rpow_two_div_le (d := d) hd
  nlinarith [hpow, hsplit, h2, hkp0]

/-- `orrw.tex`: `Φ_n ≤ C₁k^{2/d}` for `n ≤ σ_k`. -/
lemma Phi_le_bound (hd : 2 ≤ d) {C : ℝ} (hCpos : 0 < C)
    (hCmax : ∀ A : Finset (Site d), A.Nonempty →
      (∀ x ∈ A, u A x ≤ C * (A.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ∧
      (∀ x ∉ A, ORRW.h A x ≤ C * (A.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ∧
      T A ≤ C * (A.card : ℝ) ^ (1 + (2 : ℝ) / (d : ℝ)))
    (w : Fin n → Dir d) {t k : ℕ} (ht : t ≤ n) (hk1 : 1 ≤ k) (hE : (E w t).card ≤ k) :
    Phi w t ≤ 2 * (d : ℝ) * (1 + 2 * C) * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
  have hkp0 : (0 : ℝ) ≤ (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := Real.rpow_nonneg (by positivity) _
  have h2d : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  by_cases hmem : pos w t ∈ S w t
  · have hu := (hCmax (S w t) ⟨_, hmem⟩).1 (pos w t) hmem
    have hS := card_S_rpow_le hd w ht hk1 hE
    have hchain : u (S w t) (pos w t) ≤ 2 * C * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
      nlinarith [hu, hS, hCpos, hkp0]
    show 2 * (d : ℝ) * u (S w t) (pos w t) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hchain h2d, mul_nonneg h2d hkp0, hCpos]
  · show 2 * (d : ℝ) * u (S w t) (pos w t) ≤ _
    rw [u_eq_zero_of_notMem _ hmem]
    have hpos : (0 : ℝ) ≤ 2 * (d : ℝ) * (1 + 2 * C) * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
      have : (0 : ℝ) ≤ 2 * (d : ℝ) * (1 + 2 * C) := by nlinarith [hCpos]
      exact mul_nonneg this hkp0
    linarith

/-- `orrw.tex`: `γ_n ≤ C₁βk^{2/d}` for `n ≤ σ_k`. -/
lemma gamma_le_bound (hd : 2 ≤ d) {C : ℝ} (hCpos : 0 < C)
    (hCmax : ∀ A : Finset (Site d), A.Nonempty →
      (∀ x ∈ A, u A x ≤ C * (A.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ∧
      (∀ x ∉ A, ORRW.h A x ≤ C * (A.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ∧
      T A ≤ C * (A.card : ℝ) ^ (1 + (2 : ℝ) / (d : ℝ)))
    {β : ℝ} (hβ0 : 0 ≤ β)
    (w : Fin n → Dir d) {t k : ℕ} (ht : t ≤ n) (hk1 : 1 ≤ k) (hE : (E w t).card ≤ k) :
    gamma β w t ≤ 2 * (d : ℝ) * (1 + 2 * C) * β * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
  have hd1 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hkp0 : (0 : ℝ) ≤ (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hkp1 : (1 : ℝ) ≤ (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) :=
    one_le_rpow_cast hk1 (by positivity)
  have h2dβ : (0 : ℝ) ≤ 2 * (d : ℝ) * β := mul_nonneg (by positivity) hβ0
  unfold gamma
  by_cases h0 : nu w t = 0
  · rw [if_pos h0]
    have hpos : (0 : ℝ) ≤ 2 * (d : ℝ) * (1 + 2 * C) * β * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
      have h1 : (0 : ℝ) ≤ 2 * (d : ℝ) * (1 + 2 * C) := by nlinarith [hCpos]
      exact mul_nonneg (mul_nonneg h1 hβ0) hkp0
    linarith
  · rw [if_neg h0]
    have hnot : pos w t ∉ S w t := fun hc => h0 ((nu_eq_zero_iff hd1 w t).mpr hc)
    have hh : ORRW.h (S w t) (pos w t) ≤ (1 + 2 * C) * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
      rcases (S w t).eq_empty_or_nonempty with he | hne
      · have hone : ORRW.h (S w t) (pos w t) = 1 := by
          rw [he]
          unfold ORRW.h
          simp
        rw [hone]
        nlinarith [hkp1, hCpos, hkp0]
      · have hb := (hCmax (S w t) hne).2.1 (pos w t) hnot
        have hS := card_S_rpow_le hd w ht hk1 hE
        nlinarith [hb, hS, hCpos, hkp0, hkp1]
    have := mul_le_mul_of_nonneg_left hh h2dβ
    nlinarith [this]

/-! ### Proposition 5.2

`orrw.tex`.  Apply `lem:exp` to the stopped processes
`Φ_{n∧σ_k}`, `Γ_{n∧σ_k}` with `p := C₁k^{2/d}`, `q := 2C₁βk^{2/d}` and
`b := Kβk^{1+1/d}`, then take `s := 4b`. -/

set_option maxHeartbeats 2000000 in
/-- Establishes the exponential tail bound on σ_k needed for Proposition 5.2, showing the probability that the accumulated charge exceeds k decays like e^{-cN} once N dominates Kβk^{1+1/d}. -/
theorem sigma_tail_of {d : ℕ} (hd : 2 ≤ d) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ β : ℝ, 1 ≤ β → ∀ k : ℕ, 1 ≤ k → ∀ N : ℕ,
      8 * K * β * (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) ≤ (N : ℝ) →
      prb (d := d) N β
          (fun w => 8 * K * β * (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) < (sigma w k : ℝ))
        ≤ Real.exp (-(c * (k : ℝ) ^ (((d : ℝ) - 1) / (d : ℝ)))) := by
  have hd1 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := by positivity
  obtain ⟨K, hKpos, hK⟩ := ORRW.Frozen.accumulated_charge hd
  obtain ⟨C, hCpos, hCmax⟩ := ORRW.Frozen.max_exit (le_trans (by norm_num) hd)
  obtain ⟨C₁, hC₁⟩ : ∃ x : ℝ, x = 2 * (d : ℝ) * (1 + 2 * C) := ⟨_, rfl⟩
  have hC₁pos : (0 : ℝ) < C₁ := by rw [hC₁]; nlinarith [hCpos, hdR]
  refine ⟨K / (2 * (1 + 3 * C₁)), K, div_pos hKpos (by linarith), hKpos, ?_⟩
  intro β hβ k hk1 N hN
  have hβ0 : (0 : ℝ) ≤ β := le_trans zero_le_one hβ
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hkp1 : (1 : ℝ) ≤ (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) :=
    one_le_rpow_cast hk1 (by positivity)
  have hkp0 : (0 : ℝ) < (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by linarith
  obtain ⟨p, hp⟩ : ∃ x : ℝ, x = C₁ * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ x : ℝ, x = 2 * C₁ * β * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ x : ℝ, x = K * β * (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ x : ℝ, x = 1 / (4 * (1 + p + q)) := ⟨_, rfl⟩
  have hb0 : (0 : ℝ) ≤ b := by
    rw [hb]
    have : (0 : ℝ) ≤ (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) := Real.rpow_nonneg (by positivity) _
    exact mul_nonneg (mul_nonneg hKpos.le hβ0) this
  have hppos : (0 : ℝ) < p := by rw [hp]; positivity
  have hqpos : (0 : ℝ) < q := by rw [hq]; nlinarith [hC₁pos, hkp0, hβ]
  -- `|E_t| ≤ k` at every stopped time.
  have hEk : ∀ (M : ℕ) (v : Fin M → Dir d), (E v (min (sigma v k) M)).card ≤ k :=
    fun M v => card_E_le_of_le_sigma v (min_le_right _ _) (min_le_left _ _)
  -- The hypotheses of `lem:exp`.
  have hζ0 : ∀ v : Fin 0 → Dir d, min (sigma v k) 0 = 0 := fun v => Nat.min_zero _
  have hχ : ∀ (M : ℕ) (v : Fin M → Dir d),
      (if sigma v k ≤ M then 0 else 1) ≤ 1 := by
    intro M v; split <;> omega
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
  have hΦbd : ∀ (M : ℕ) (v : Fin M → Dir d),
      0 ≤ Phi v (min (sigma v k) M) ∧ Phi v (min (sigma v k) M) ≤ p := by
    intro M v
    refine ⟨Phi_nonneg hd1 v _, ?_⟩
    rw [hp, hC₁]
    exact Phi_le_bound hd hCpos hCmax v (min_le_right _ _) hk1 (hEk M v)
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
  have hδ : ∀ (M : ℕ) (v : Fin M → Dir d) (a : Dir d),
      0 ≤ Gamma β (Fin.snoc v a) (min (sigma (Fin.snoc v a) k) (M + 1))
            - Gamma β v (min (sigma v k) M) ∧
      Gamma β (Fin.snoc v a) (min (sigma (Fin.snoc v a) k) (M + 1))
            - Gamma β v (min (sigma v k) M) ≤ q := by
    intro M v a
    by_cases hcase : sigma v k ≤ M
    · have hs : sigma (Fin.snoc v a) k = sigma v k := sigma_snoc_of_le v a hcase
      rw [show min (sigma (Fin.snoc v a) k) (M + 1) = sigma v k by rw [hs]; omega,
        show min (sigma v k) M = sigma v k by omega, Gamma_snoc hd1 β v a _ hcase]
      constructor
      · simp
      · have : Gamma β v (sigma v k) - Gamma β v (sigma v k) = 0 := by ring
        rw [this]
        exact hqpos.le
    · push_neg at hcase
      have hs : M + 1 ≤ sigma (Fin.snoc v a) k := sigma_snoc_of_lt v a hcase
      rw [show min (sigma (Fin.snoc v a) k) (M + 1) = M + 1 by omega,
        show min (sigma v k) M = M by omega, ← Gamma_snoc hd1 β v a M (le_refl M)]
      have hstep : Gamma β (Fin.snoc v a) (M + 1)
          = Gamma β (Fin.snoc v a) M
            + eta (Fin.snoc v a) (M + 1)
              * (gamma β (Fin.snoc v a) M + Phi (Fin.snoc v a) (M + 1)) := rfl
      rw [hstep]
      have hEM : (E (Fin.snoc v a) M).card ≤ k := by
        rw [E_snoc v a (le_refl M)]
        exact le_of_lt (card_E_lt_of_lt_sigma v hcase (le_refl M))
      have hEM1 : (E (Fin.snoc v a) (M + 1)).card ≤ k :=
        card_E_le_of_le_sigma (Fin.snoc v a) (le_refl (M + 1)) hs
      have hg0 : 0 ≤ gamma β (Fin.snoc v a) M := gamma_nonneg hd1 hβ0 _ _
      have hf0 : 0 ≤ Phi (Fin.snoc v a) (M + 1) := Phi_nonneg hd1 _ _
      have he0 : 0 ≤ eta (Fin.snoc v a) (M + 1) := eta_nonneg _ _
      have he1 : eta (Fin.snoc v a) (M + 1) ≤ 1 := eta_le_one _ _
      have hgb : gamma β (Fin.snoc v a) M
          ≤ 2 * (d : ℝ) * (1 + 2 * C) * β * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) :=
        gamma_le_bound hd hCpos hCmax hβ0 (Fin.snoc v a) (by omega) hk1 hEM
      have hfb : Phi (Fin.snoc v a) (M + 1)
          ≤ 2 * (d : ℝ) * (1 + 2 * C) * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) :=
        Phi_le_bound hd hCpos hCmax (Fin.snoc v a) (le_refl (M + 1)) hk1 hEM1
      rw [← hC₁] at hgb hfb
      constructor
      · have : Gamma β (Fin.snoc v a) M
              + eta (Fin.snoc v a) (M + 1)
                * (gamma β (Fin.snoc v a) M + Phi (Fin.snoc v a) (M + 1))
            - Gamma β (Fin.snoc v a) M
            = eta (Fin.snoc v a) (M + 1)
                * (gamma β (Fin.snoc v a) M + Phi (Fin.snoc v a) (M + 1)) := by ring
        rw [this]
        exact mul_nonneg he0 (by linarith)
      · have heq : Gamma β (Fin.snoc v a) M
              + eta (Fin.snoc v a) (M + 1)
                * (gamma β (Fin.snoc v a) M + Phi (Fin.snoc v a) (M + 1))
            - Gamma β (Fin.snoc v a) M
            = eta (Fin.snoc v a) (M + 1)
                * (gamma β (Fin.snoc v a) M + Phi (Fin.snoc v a) (M + 1)) := by ring
        rw [heq, hq]
        nlinarith [hgb, hfb, he0, he1, hg0, hf0, hC₁pos, hkp0, hβ]
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
  -- `lem:exp`.
  have key := ORRW.Frozen.time_versus_charge (d := d) hd1 hβ
    (fun M v => Phi v (min (sigma v k) M))
    (fun M v => Gamma β v (min (sigma v k) M))
    (fun M v => min (sigma v k) M)
    (fun M v => if sigma v k ≤ M then 0 else 1)
    p q b θ hζ0 hχ hζ hΦ0 hΓ0 hΦbd hδ hΓbd hdrift hθ
  have htail := key.2 N (4 * b) (by linarith)
  -- The event inclusion.
  have hincl : prb (d := d) N β
      (fun w => 8 * K * β * (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) < (sigma w k : ℝ))
      ≤ prb (d := d) N β (fun w => 4 * b + 4 * b ≤ ((min (sigma w k) N : ℕ) : ℝ)) := by
    refine prb_mono hd1 hβ _ _ ?_
    intro w hw
    rw [Nat.cast_min]
    have h8 : 4 * b + 4 * b = 8 * K * β * (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) := by
      rw [hb]; ring
    rw [h8]
    exact le_min (le_of_lt hw) hN
  -- The exponent.
  have hApos : (0 : ℝ) < β * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
    have : (0 : ℝ) < β := by linarith
    exact mul_pos this hkp0
  have hDpos : (0 : ℝ) < 1 + 3 * C₁ := by linarith
  have hpq : 1 + p + q ≤ (1 + 3 * C₁) * (β * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ))) := by
    rw [hp, hq]
    nlinarith [hβ, hkp1, hC₁pos, hkp0]
  have hden : (0 : ℝ) < 4 * (1 + p + q) := by linarith
  have hθge : 1 / (4 * ((1 + 3 * C₁) * (β * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ))))) ≤ θ := by
    rw [hθ]
    apply one_div_le_one_div_of_le hden
    linarith
  have hkexp : (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ))
      = (k : ℝ) ^ (((d : ℝ) - 1) / (d : ℝ)) * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
    rw [← Real.rpow_add hkpos]
    congr 1
    field_simp
    ring
  have hkq0 : (0 : ℝ) ≤ (k : ℝ) ^ (((d : ℝ) - 1) / (d : ℝ)) := Real.rpow_nonneg hkpos.le _
  have hmain : K / (2 * (1 + 3 * C₁)) * (k : ℝ) ^ (((d : ℝ) - 1) / (d : ℝ))
      ≤ θ * (4 * b) / 2 := by
    have hfac : θ * (4 * b) / 2
        = 2 * θ * K * β * (k : ℝ) ^ (((d : ℝ) - 1) / (d : ℝ))
            * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
      rw [hb, hkexp]; ring
    have hstep : K / (2 * (1 + 3 * C₁))
        ≤ 2 * θ * K * β * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_right hθge
        (by positivity : (0 : ℝ) ≤ 2 * K * (β * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ))))
      have heq : 1 / (4 * ((1 + 3 * C₁) * (β * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)))))
            * (2 * K * (β * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ))))
          = K / (2 * (1 + 3 * C₁)) := by
        field_simp
        ring
      rw [heq] at hmul
      calc K / (2 * (1 + 3 * C₁))
          ≤ θ * (2 * K * (β * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)))) := hmul
        _ = 2 * θ * K * β * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by ring
    rw [hfac]
    calc K / (2 * (1 + 3 * C₁)) * (k : ℝ) ^ (((d : ℝ) - 1) / (d : ℝ))
        ≤ (2 * θ * K * β * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)))
            * (k : ℝ) ^ (((d : ℝ) - 1) / (d : ℝ)) :=
          mul_le_mul_of_nonneg_right hstep hkq0
      _ = 2 * θ * K * β * (k : ℝ) ^ (((d : ℝ) - 1) / (d : ℝ))
            * (k : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by ring
  refine le_trans hincl (le_trans htail ?_)
  exact Real.exp_le_exp.mpr (by linarith)

end ORRW.Support
