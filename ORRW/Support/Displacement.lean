/-
Proposition 6.1 of Bou-Rabee--Peres (`prop:displacement`, `orrw.tex`):
displacement and exit times.

The exit-time bound is the paper's: if the walk has stayed in the box of radius
`r` through time `m` then `|R_m| ≤ (2r+1)^d` by `eq:range-box`, so
`|E_m| ≤ d(2r+1)^d` by `eq:edges-sites` and `m < σ_{k_r}` for
`k_r := d(2r+1)^d + 1`; summing over `m < N` turns the sum of survival
probabilities into `E_β[σ_{k_r} ∧ N]`, which `eq:sigma-mean` bounds.

The displacement bound is the paper's as well: on the event
`{|R_n| ≥ a/(2d)}` of probability at least `1/2`, `eq:range-box` forces
`Λ_n ≥ ((a/(2d))^{1/d} - 3)/2`.

Nothing in this file is frozen.
-/
import ORRW.Support.RangeLower
import ORRW.Support.RangeBox

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW.Support

open Finset ORRW

variable {d : ℕ}

/-! ### The exit time -/

set_option maxHeartbeats 1000000 in
/-- `E_β[τ_{B_r} ∧ N] ≤ Cβ(2r+1)^{d+1}`, uniformly in the horizon `N`. -/
theorem exit_time_bound (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 1 ≤ β → ∀ r N : ℕ,
      ∑ m ∈ Finset.range N,
          prb (d := d) N β (fun w => ∀ j ≤ m, ‖pos w j‖ ≤ (r : ℝ))
        ≤ C * β * (2 * (r : ℝ) + 1) ^ (d + 1) := by
  classical
  have hd1 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdRpos : (0 : ℝ) < (d : ℝ) := by linarith
  obtain ⟨K, hKpos, hK⟩ := expect_min_sigma_le hd
  have hDpos : (0 : ℝ) < (2 * (d : ℝ)) ^ (1 + (1 : ℝ) / (d : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  refine ⟨K * (2 * (d : ℝ)) ^ (1 + (1 : ℝ) / (d : ℝ)), mul_pos hKpos hDpos, ?_⟩
  intro β hβ r N
  have hβpos : (0 : ℝ) < β := lt_of_lt_of_le one_pos hβ
  obtain ⟨kr, hkr⟩ : ∃ m : ℕ, m = d * (2 * r + 1) ^ d + 1 := ⟨_, rfl⟩
  -- Staying in the box through time `m` forces `m < σ_{k_r}`.
  have hmono : ∑ m ∈ Finset.range N,
        prb (d := d) N β (fun w => ∀ j ≤ m, ‖pos w j‖ ≤ (r : ℝ))
      ≤ ∑ m ∈ Finset.range N,
        prb (d := d) N β (fun w => m < min (sigma w kr) N) := by
    refine Finset.sum_le_sum fun m hm => ?_
    refine prb_mono hd1 hβ _ _ ?_
    intro w hP
    have hmN : m < N := Finset.mem_range.mp hm
    have hbox : (R w m).card ≤ (2 * r + 1) ^ d := card_range_le_box w m r hP
    have hE : (E w m).card < kr := by
      have h1 : (E w m).card ≤ d * (R w m).card := ORRW.card_edges_le_card_range w m
      have h2 : d * (R w m).card ≤ d * (2 * r + 1) ^ d := Nat.mul_le_mul_left d hbox
      omega
    have hnot : ¬ (sigma w kr ≤ m) := by
      intro hc
      exact absurd ((sigma_le_iff w (le_of_lt hmN)).mp hc) (by omega)
    omega
  -- The sum of the survival probabilities is `E_β[σ_{k_r} ∧ N]`.
  have heq : ∑ m ∈ Finset.range N,
        prb (d := d) N β (fun w => m < min (sigma w kr) N)
      = expect (d := d) N β (fun w => ((min (sigma w kr) N : ℕ) : ℝ)) := by
    have h1 : ∀ m : ℕ, prb (d := d) N β (fun w => m < min (sigma w kr) N)
        = expect (d := d) N β
            (fun w => if m < min (sigma w kr) N then (1 : ℝ) else 0) :=
      fun m => prb_eq_expect_indicator β _
    rw [Finset.sum_congr rfl (fun m _ => h1 m), expect_sum]
    refine expect_congr β fun w => ?_
    rw [Finset.sum_boole]
    congr 1
    have hfil : {m ∈ Finset.range N | m < min (sigma w kr) N}
        = Finset.range (min (sigma w kr) N) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfil, Finset.card_range]
  -- The arithmetic of `k_r ≤ 2d(2r+1)^d`.
  have hX : (0 : ℝ) < 2 * (r : ℝ) + 1 := by positivity
  have hkrle : (kr : ℝ) ≤ 2 * (d : ℝ) * (2 * (r : ℝ) + 1) ^ d := by
    have hone : (1 : ℝ) ≤ (2 * (r : ℝ) + 1) ^ d := one_le_pow₀ (by linarith)
    rw [hkr]
    push_cast
    nlinarith [hone, hdR]
  have hexp2 : (d : ℝ) * (1 + (1 : ℝ) / (d : ℝ)) = ((d + 1 : ℕ) : ℝ) := by
    have hd0 : (d : ℝ) ≠ 0 := by linarith
    push_cast
    field_simp
  have hnat : ((2 * (r : ℝ) + 1) ^ d) ^ (1 + (1 : ℝ) / (d : ℝ))
      = (2 * (r : ℝ) + 1) ^ (d + 1) := by
    rw [← Real.rpow_natCast (2 * (r : ℝ) + 1) d, ← Real.rpow_mul hX.le, hexp2,
      Real.rpow_natCast]
  have harith : K * β * (kr : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ))
      ≤ K * (2 * (d : ℝ)) ^ (1 + (1 : ℝ) / (d : ℝ)) * β * (2 * (r : ℝ) + 1) ^ (d + 1) := by
    have hpow : (kr : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ))
        ≤ (2 * (d : ℝ) * (2 * (r : ℝ) + 1) ^ d) ^ (1 + (1 : ℝ) / (d : ℝ)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg kr) hkrle (by positivity)
    have hsplit : (2 * (d : ℝ) * (2 * (r : ℝ) + 1) ^ d) ^ (1 + (1 : ℝ) / (d : ℝ))
        = (2 * (d : ℝ)) ^ (1 + (1 : ℝ) / (d : ℝ)) * ((2 * (r : ℝ) + 1) ^ d) ^ (1 + (1 : ℝ) / (d : ℝ)) :=
      Real.mul_rpow (by linarith) (by positivity)
    have hKβ : (0 : ℝ) ≤ K * β := by positivity
    have := mul_le_mul_of_nonneg_left hpow hKβ
    rw [hsplit, hnat] at this
    calc K * β * (kr : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ))
        ≤ K * β * ((2 * (d : ℝ)) ^ (1 + (1 : ℝ) / (d : ℝ)) * (2 * (r : ℝ) + 1) ^ (d + 1)) := this
      _ = K * (2 * (d : ℝ)) ^ (1 + (1 : ℝ) / (d : ℝ)) * β * (2 * (r : ℝ) + 1) ^ (d + 1) := by
          ring
  rw [heq] at hmono
  exact le_trans hmono (le_trans (hK β hβ kr N) harith)

/-! ### The displacement -/

/-- Every unit step has sup norm at least one. -/
theorem one_le_norm_dirVec (a : Dir d) : (1 : ℝ) ≤ ‖dirVec a‖ := by
  have hco : ‖dirVec a a.1‖ ≤ ‖dirVec a‖ := norm_le_pi_norm (dirVec a) a.1
  have hval : ‖dirVec a a.1‖ = 1 := by
    rw [dirVec_apply]
    cases a.2 <;> simp
  linarith [hco, hval.le, hval.ge]

set_option maxHeartbeats 1000000 in
/-- `E_β Λ_n ≥ cβ^{-1/(d+1)}n^{1/(d+1)}`, the paper's displacement bound. -/
theorem displacement_bound (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ,
      c * β ^ (-((1 : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1))
        ≤ expect (d := d) n β
            (fun w => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              (fun k => ‖pos w k‖)) := by
  have hd1 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdRpos : (0 : ℝ) < (d : ℝ) := by linarith
  obtain ⟨K, hKpos, hhalf⟩ := half_le_prb_range hd
  obtain ⟨p, hp⟩ : ∃ x : ℝ, x = (1 : ℝ) / ((d : ℝ) + 1) := ⟨_, rfl⟩
  have hppos : (0 : ℝ) < p := by rw [hp]; positivity
  have hA : (0 : ℝ) < 2 * K := by linarith
  obtain ⟨G, hG⟩ : ∃ x : ℝ, x = (2 * (d : ℝ)) ^ ((1 : ℝ) / (d : ℝ)) * (2 * K) ^ p := ⟨_, rfl⟩
  have hGpos : (0 : ℝ) < G := by
    rw [hG]
    exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos hA _)
  obtain ⟨M, hM⟩ : ∃ x : ℝ, x = max (2 * K) ((6 * G) ^ (d + 1)) := ⟨_, rfl⟩
  have hMpos : (0 : ℝ) < M := by rw [hM]; exact lt_of_lt_of_le hA (le_max_left _ _)
  have hMp : (0 : ℝ) < M ^ p := Real.rpow_pos_of_pos hMpos p
  refine ⟨min (1 / (8 * G)) (1 / M ^ p),
    lt_min (by positivity) (by positivity), ?_⟩
  intro β hβ n
  rw [← hp]
  have hβpos : (0 : ℝ) < β := lt_of_lt_of_le one_pos hβ
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  set L : (Fin n → Dir d) → ℝ :=
    fun w => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      (fun k => ‖pos w k‖) with hL
  have hLle : ∀ (w : Fin n → Dir d) (j : ℕ), j ≤ n → ‖pos w j‖ ≤ L w := by
    intro w j hj
    rw [hL]
    exact Finset.le_sup' (fun k => ‖pos w k‖) (Finset.mem_range.mpr (by omega))
  have hL0 : ∀ w : Fin n → Dir d, (0 : ℝ) ≤ L w :=
    fun w => le_trans (norm_nonneg _) (hLle w 0 (Nat.zero_le n))
  -- `y = (n/β)^{1/(d+1)}` is the quantity to be bounded from below.
  obtain ⟨y, hy⟩ : ∃ x : ℝ, x = ((n : ℝ) / β) ^ p := ⟨_, rfl⟩
  have hy0 : (0 : ℝ) ≤ y := by rw [hy]; exact Real.rpow_nonneg (by positivity) p
  have hlhs : β ^ (-p) * (n : ℝ) ^ p = y := by
    rw [hy, Real.div_rpow hn0 hβpos.le, Real.rpow_neg hβpos.le]
    field_simp
  have hgoal : min (1 / (8 * G)) (1 / M ^ p) * β ^ (-p) * (n : ℝ) ^ p
      = min (1 / (8 * G)) (1 / M ^ p) * y := by rw [← hlhs]; ring
  rw [hgoal]
  -- `eq:range-box`, with the ceiling absorbed into the constant `3`.
  have hbox : ∀ w : Fin n → Dir d, ((R w n).card : ℝ) ≤ (2 * L w + 3) ^ d := by
    intro w
    have hceil : ∀ j ≤ n, ‖pos w j‖ ≤ ((⌈L w⌉₊ : ℕ) : ℝ) :=
      fun j hj => le_trans (hLle w j hj) (Nat.le_ceil _)
    have h1 : (R w n).card ≤ (2 * ⌈L w⌉₊ + 1) ^ d := card_range_le_box w n ⌈L w⌉₊ hceil
    have h2 : ((R w n).card : ℝ) ≤ (2 * (⌈L w⌉₊ : ℝ) + 1) ^ d := by
      have hc := (Nat.cast_le (α := ℝ)).mpr h1
      push_cast at hc
      exact hc
    have h3 : 2 * (⌈L w⌉₊ : ℝ) + 1 ≤ 2 * L w + 3 := by
      have := Nat.ceil_lt_add_one (hL0 w)
      linarith
    have h4 : (2 * (⌈L w⌉₊ : ℝ) + 1) ^ d ≤ (2 * L w + 3) ^ d :=
      pow_le_pow_left₀ (by positivity) h3 d
    linarith
  by_cases hcase : M * β ≤ (n : ℝ)
  · -- The main case.
    have h2K : 2 * K * β ≤ (n : ℝ) := by
      have hle : 2 * K ≤ M := by rw [hM]; exact le_max_left _ _
      nlinarith [hβpos]
    have hgood := hhalf β hβ n h2K
    obtain ⟨a, ha⟩ : ∃ x : ℝ, x = ((n : ℝ) / (2 * K * β)) ^ ((d : ℝ) / ((d : ℝ) + 1)) := ⟨_, rfl⟩
    rw [← ha] at hgood
    have ha0 : (0 : ℝ) ≤ a := by rw [ha]; exact Real.rpow_nonneg (by positivity) _
    obtain ⟨t, ht⟩ : ∃ x : ℝ, x = a / (2 * (d : ℝ)) := ⟨_, rfl⟩
    rw [← ht] at hgood
    have ht0 : (0 : ℝ) ≤ t := by rw [ht]; positivity
    -- `t^{1/d} = y/G`.
    have hedp : (d : ℝ) / ((d : ℝ) + 1) * ((1 : ℝ) / (d : ℝ)) = p := by
      rw [hp]
      have h1 : (d : ℝ) ≠ 0 := by linarith
      have h2 : (d : ℝ) + 1 ≠ 0 := by linarith
      field_simp
    have htG : t ^ ((1 : ℝ) / (d : ℝ)) = y / G := by
      rw [ht, Real.div_rpow ha0 (by linarith), ha, ← Real.rpow_mul (by positivity), hedp,
        hy, hG]
      have hsplit : (n : ℝ) / (2 * K * β) = ((n : ℝ) / β) / (2 * K) := by
        field_simp
      rw [hsplit, Real.div_rpow (by positivity) hA.le]
      have h1 : ((2 * K) ^ p) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hA p)
      have h2 : ((2 * (d : ℝ)) ^ ((1 : ℝ) / (d : ℝ))) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)
      field_simp
    -- `y ≥ 6G`.
    have hd1p : ((d + 1 : ℕ) : ℝ) * p = 1 := by
      rw [hp]
      have h2 : (d : ℝ) + 1 ≠ 0 := by linarith
      push_cast
      field_simp
    have hy6 : 6 * G ≤ y := by
      have hMn : (6 * G) ^ (d + 1) ≤ M := by rw [hM]; exact le_max_right _ _
      have hnb : (6 * G) ^ (d + 1) ≤ (n : ℝ) / β := by
        rw [le_div_iff₀ hβpos]
        nlinarith [hcase, hβpos]
      have h1 : ((6 * G) ^ (d + 1) : ℝ) ^ p ≤ ((n : ℝ) / β) ^ p :=
        Real.rpow_le_rpow (by positivity) hnb hppos.le
      have h2 : (((6 * G : ℝ)) ^ (d + 1)) ^ p = 6 * G := by
        rw [← Real.rpow_natCast (6 * G) (d + 1), ← Real.rpow_mul (by positivity), hd1p,
          Real.rpow_one]
      rw [hy]
      linarith [h1, h2.le, h2.ge]
    -- On the event `{|R_n| ≥ t}` the displacement is at least `y/(4G)`.
    have hev : ∀ w : Fin n → Dir d, t ≤ ((R w n).card : ℝ) → y / (4 * G) ≤ L w := by
      intro w hw
      have h1 : t ≤ (2 * L w + 3) ^ d := le_trans hw (hbox w)
      have h2 : t ^ ((1 : ℝ) / (d : ℝ)) ≤ ((2 * L w + 3) ^ d) ^ ((1 : ℝ) / (d : ℝ)) :=
        Real.rpow_le_rpow ht0 h1 (by positivity)
      have h3 : ((2 * L w + 3 : ℝ) ^ (d : ℕ)) ^ ((1 : ℝ) / (d : ℝ)) = 2 * L w + 3 := by
        rw [← Real.rpow_natCast (2 * L w + 3) d,
          ← Real.rpow_mul (by linarith [hL0 w]),
          show (d : ℝ) * ((1 : ℝ) / (d : ℝ)) = 1 by field_simp, Real.rpow_one]
      rw [htG, h3] at h2
      rw [div_le_iff₀ hGpos] at h2
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * G)]
      nlinarith [h2, hy6, hGpos]
    have hprb : (1 : ℝ) / 2 ≤ prb (d := d) n β (fun w => y / (4 * G) ≤ L w) :=
      le_trans hgood (prb_mono hd1 hβ _ _ hev)
    have hmk := mul_prb_le_expect (N := n) hd1 hβ L hL0 (y / (4 * G))
    have hstep : y / (4 * G) * ((1 : ℝ) / 2) ≤ expect (d := d) n β L :=
      le_trans (mul_le_mul_of_nonneg_left hprb (by positivity)) hmk
    have hc1 : min (1 / (8 * G)) (1 / M ^ p) ≤ 1 / (8 * G) := min_le_left _ _
    have hfin : min (1 / (8 * G)) (1 / M ^ p) * y ≤ y / (4 * G) * ((1 : ℝ) / 2) := by
      have h1 : min (1 / (8 * G)) (1 / M ^ p) * y ≤ 1 / (8 * G) * y :=
        mul_le_mul_of_nonneg_right hc1 hy0
      have h2 : 1 / (8 * G) * y = y / (4 * G) * ((1 : ℝ) / 2) := by
        field_simp
        ring
      linarith
    linarith
  · -- The degenerate case `n < Mβ`.
    push_neg at hcase
    have hyM : y ≤ M ^ p := by
      rw [hy]
      refine Real.rpow_le_rpow (by positivity) ?_ hppos.le
      rw [div_le_iff₀ hβpos]
      linarith
    have hc2 : min (1 / (8 * G)) (1 / M ^ p) ≤ 1 / M ^ p := min_le_right _ _
    have hcnn : (0 : ℝ) ≤ min (1 / (8 * G)) (1 / M ^ p) :=
      le_of_lt (lt_min (by positivity) (by positivity))
    have hsmall : min (1 / (8 * G)) (1 / M ^ p) * y ≤ 1 := by
      have h1 : min (1 / (8 * G)) (1 / M ^ p) * y ≤ 1 / M ^ p * M ^ p :=
        mul_le_mul hc2 hyM hy0 (by positivity)
      have h2 : 1 / M ^ p * M ^ p = 1 := by field_simp
      linarith
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have hyz : y = 0 := by
        rw [hy, hn]
        simp [Real.zero_rpow (ne_of_gt hppos)]
      rw [hyz, mul_zero]
      have hz : expect (d := d) n β (fun _ => (0 : ℝ)) = 0 := by
        unfold expect
        simp
      have hmono := expect_mono hd1 hβ (fun _ => (0 : ℝ)) L (fun w => hL0 w)
      linarith [hz.le, hz.ge]
    · have hL1 : ∀ w : Fin n → Dir d, (1 : ℝ) ≤ L w := by
        intro w
        have hstep : pos w 1 = dirVec (w ⟨0, hn⟩) := by
          have h := pos_succ w 0 hn
          simpa [pos_zero] using h
        have h1 : (1 : ℝ) ≤ ‖pos w 1‖ := by
          rw [hstep]
          exact one_le_norm_dirVec _
        exact le_trans h1 (hLle w 1 hn)
      have hmono := expect_mono hd1 hβ (fun _ => (1 : ℝ)) L hL1
      rw [expect_one hd1 hβ] at hmono
      linarith

/-! ### Proposition 6.1 -/

/-- The two displayed bounds of `prop:displacement`. -/
theorem displacement_of (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ β : ℝ, 1 ≤ β →
      (∀ r N : ℕ,
          ∑ m ∈ Finset.range N,
              prb (d := d) N β (fun w => ∀ j ≤ m, ‖pos w j‖ ≤ (r : ℝ))
            ≤ C * β * (2 * (r : ℝ) + 1) ^ (d + 1)) ∧
      (∀ n : ℕ,
          c * β ^ (-((1 : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1))
            ≤ expect (d := d) n β
                (fun w => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
                  (fun k => ‖pos w k‖))) := by
  obtain ⟨C, hCpos, hC⟩ := exit_time_bound hd
  obtain ⟨c, hcpos, hc⟩ := displacement_bound hd
  exact ⟨c, C, hcpos, hCpos, fun β hβ => ⟨hC β hβ, hc β hβ⟩⟩

end ORRW.Support
