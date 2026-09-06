/-
Supporting lemmas for Lemma 3.1 of Bou-Rabee--Peres (`lem:martingale`,
`orrw.tex`): the one-step drift of `n + Φ_n - Γ_n`.

Nothing here is frozen.  The file has three parts.

* How the processes of `ORRW/Potential.lean` behave under appending a letter.
  Under ruling R-001 a history of length `m` is a word `v : Fin m → Dir d` and
  the possible continuations are the words `Fin.snoc v a`, so every quantity of
  Section 3 evaluated at time `m` or `m + 1` has to be read along `Fin.snoc v a`.
  All the time-`m` quantities are independent of `a` (`ORRW.pos_init`,
  `ORRW.E_init`), and the time-`(m+1)` ones are computed explicitly.

* The two cases of the paper's proof, `orrw.tex`, as exact evaluations
  of the numerator of the drift.

* The drift bound itself, `eq:drift`.
-/
import ORRW.Potential
import ORRW.Support.Insertion
import ORRW.Support.Thomson

namespace ORRW.Support

open Finset ORRW

variable {d m n : ℕ}

/-! ### Appending a letter -/

/-- The position at a time within the old horizon does not see the new letter. -/
lemma pos_snoc (v : Fin m → Dir d) (a : Dir d) {k : ℕ} (hk : k ≤ m) :
    pos (Fin.snoc v a) k = pos v k := by
  have h := ORRW.pos_init (Fin.snoc v a) hk
  rw [Fin.init_snoc] at h
  exact h.symm

/-- The traversed-edge set at a time within the old horizon does not see the new
letter. -/
lemma E_snoc (v : Fin m → Dir d) (a : Dir d) {k : ℕ} (hk : k ≤ m) :
    E (Fin.snoc v a) k = E v k := by
  have h := ORRW.E_init (Fin.snoc v a) hk
  rw [Fin.init_snoc] at h
  exact h.symm

/-- The new letter is the step taken: `X_{m+1} = X_m + dirVec a`. -/
lemma pos_snoc_last (v : Fin m → Dir d) (a : Dir d) :
    pos (Fin.snoc v a) (m + 1) = pos v m + dirVec a := by
  rw [ORRW.pos_succ (Fin.snoc v a) m (Nat.lt_succ_self m), pos_snoc v a (le_refl m)]
  have h1 : (Fin.snoc v a : Fin (m+1) → Dir d) ⟨m, Nat.lt_succ_self m⟩ = a := by
    have h : (⟨m, Nat.lt_succ_self m⟩ : Fin (m+1)) = Fin.last m := rfl
    rw [h, Fin.snoc_last]
  rw [h1]

/-- One step adds at most the edge it crosses. -/
lemma E_snoc_succ (v : Fin m → Dir d) (a : Dir d) :
    E (Fin.snoc v a) (m + 1) = insert s(pos v m, pos v m + dirVec a) (E v m) := by
  unfold E
  rw [Nat.min_self, Finset.range_add_one, Finset.image_insert]
  congr 1
  · unfold edgeAt
    rw [pos_snoc v a (le_refl m), pos_snoc_last v a]
  · rw [show (Finset.range m).image (edgeAt (Fin.snoc v a))
        = E (Fin.snoc v a) m by unfold E; rw [Nat.min_eq_left (Nat.le_succ m)]]
    exact E_snoc v a (le_refl m)

/-- A step along a traversed edge leaves `E` unchanged. -/
lemma E_snoc_succ_of_mem (v : Fin m → Dir d) (a : Dir d)
    (ha : s(pos v m, pos v m + dirVec a) ∈ E v m) :
    E (Fin.snoc v a) (m + 1) = E v m := by
  rw [E_snoc_succ, Finset.insert_eq_self.mpr ha]

/-- `S` depends on the word only through `E`, for `d ≥ 1` (ruling P-002). -/
lemma S_eq_of_E_eq (hd : 0 < d) {n₁ n₂ : ℕ} (w₁ : Fin n₁ → Dir d) (w₂ : Fin n₂ → Dir d)
    {k₁ k₂ : ℕ} (hE : E w₁ k₁ = E w₂ k₂) : S w₁ k₁ = S w₂ k₂ := by
  ext x
  rw [mem_S_iff hd, mem_S_iff hd, hE]

/-- Computes the site weight of the extended history after appending a letter, showing it equals the old weight plus one when the new edge lands on a fresh site within the previously visited range. -/
lemma S_snoc (hd : 0 < d) (v : Fin m → Dir d) (a : Dir d) {k : ℕ} (hk : k ≤ m) :
    S (Fin.snoc v a) k = S v k :=
  S_eq_of_E_eq hd _ _ (E_snoc v a hk)

/-- Computes the site weight ν at time m + 1 along the extended history by showing it splits into the time-m contribution plus an indicator that the appended step lands within the first k sites. -/
lemma nu_snoc (v : Fin m → Dir d) (a : Dir d) {k : ℕ} (hk : k ≤ m) :
    nu (Fin.snoc v a) k = nu v k := by
  unfold nu
  rw [pos_snoc v a hk, E_snoc v a hk]

/-- Relates the potential at time m+1 along the extended history to the potential at time m, giving the one-step update needed for the drift computation. -/
lemma Phi_snoc (hd : 0 < d) (v : Fin m → Dir d) (a : Dir d) {k : ℕ} (hk : k ≤ m) :
    Phi (Fin.snoc v a) k = Phi v k := by
  unfold Phi
  rw [S_snoc hd v a hk, pos_snoc v a hk]

/-- Computes the charge Γ at the next time along the extended walk, used to evaluate the drift of n + Φ − Γ. -/
lemma gamma_snoc (hd : 0 < d) (β : ℝ) (v : Fin m → Dir d) (a : Dir d) {k : ℕ} (hk : k ≤ m) :
    gamma β (Fin.snoc v a) k = gamma β v k := by
  unfold gamma
  rw [S_snoc hd v a hk, pos_snoc v a hk, nu_snoc v a hk]

/-- A step along a traversed edge pays no charge. -/
lemma eta_snoc_of_mem (v : Fin m → Dir d) (a : Dir d)
    (ha : s(pos v m, pos v m + dirVec a) ∈ E v m) :
    eta (Fin.snoc v a) (m + 1) = 0 := by
  unfold eta
  simp only [Nat.add_sub_cancel]
  rw [if_neg]
  rw [E_snoc v a (le_refl m), E_snoc_succ_of_mem v a ha]
  exact lt_irrefl _

/-- A step crossing an untraversed edge pays a charge. -/
lemma eta_snoc_of_notMem (v : Fin m → Dir d) (a : Dir d)
    (ha : s(pos v m, pos v m + dirVec a) ∉ E v m) :
    eta (Fin.snoc v a) (m + 1) = 1 := by
  unfold eta
  simp only [Nat.add_sub_cancel]
  rw [if_pos]
  rw [E_snoc v a (le_refl m), E_snoc_succ, Finset.card_insert_of_notMem ha]
  omega

/-- `orrw.tex`: "A neighbor of `X_n` that lies in `S_n` is joined to
`X_n` by a traversed edge."  Contrapositive form. -/
lemma notMem_S_of_untraversed (hd : 0 < d) (v : Fin m → Dir d) (a : Dir d)
    (ha : s(pos v m, pos v m + dirVec a) ∉ E v m) :
    pos v m + dirVec a ∉ S v m := by
  intro hmem
  refine ha ?_
  have h := (mem_S_iff hd v m _).mp hmem (a.1, !a.2)
  rw [ORRW.Support.dirVec_neg a] at h
  have hback : pos v m + dirVec a + -dirVec a = pos v m := by abel
  rw [hback] at h
  rwa [Sym2.eq_swap] at h

/-- When `ν_m = 0` every edge at `X_m` is traversed. -/
lemma traversed_of_nu_zero (v : Fin m → Dir d) (h0 : nu v m = 0) (a : Dir d) :
    s(pos v m, pos v m + dirVec a) ∈ E v m := by
  unfold nu at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  simpa using h0 (Finset.mem_univ a)

/-! ### Elementary bounds on `μ` -/

/-- This records that the potential of a finite set of sites vanishes off that set, so the drift bound only ever involves sites in the range. -/
lemma u_eq_zero_of_notMem (A : Finset (Site d)) {y : Site d} (hy : y ∉ A) : u A y = 0 :=
  extendZero_of_notMem A _ hy

/-- Counts the available directions at a site, the constant entering the one-step drift computation. -/
lemma card_dir (d : ℕ) : (Finset.univ : Finset (Dir d)).card = 2 * d := by
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-- Bounds the number of sites in the range whose weight is at most k by twice the dimension, a uniform estimate used when controlling the drift of the martingale. -/
lemma nu_le (w : Fin n → Dir d) (k : ℕ) : nu w k ≤ 2 * d := by
  unfold nu
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [card_dir]

/-- The drift numerator stays positive, which is what makes the martingale argument of Lemma 3.1 go through. -/
lemma mu_pos (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) (w : Fin n → Dir d) (k : ℕ) :
    0 < mu β w k := by
  rw [mu_eq_totalWeight]
  exact totalWeight_pos hd hβ w k

/-- `orrw.tex`: "`μ_n` is the total weight there, so that `μ_n ≤ 2dβ`." -/
lemma mu_le {β : ℝ} (hβ : 1 ≤ β) (w : Fin n → Dir d) (k : ℕ) :
    mu β w k ≤ 2 * (d : ℝ) * β := by
  have h1 : ((nu w k : ℕ) : ℝ) ≤ 2 * (d : ℝ) := by
    have h := nu_le w k
    have h' : ((nu w k : ℕ) : ℝ) ≤ ((2 * d : ℕ) : ℝ) := Nat.cast_le.mpr h
    push_cast at h'
    linarith
  have h2 : (0 : ℝ) ≤ (nu w k : ℝ) := Nat.cast_nonneg _
  unfold mu
  nlinarith

/-- `orrw.tex` (`eq:h-def`) read over directions: the sum of `u_A` over
the `2d` neighbours of `x` is `h_A(x) - 1`. -/
lemma sum_u_nbr (A : Finset (Site d)) (x : Site d) :
    ∑ a : Dir d, u A (x + dirVec a) = ORRW.h A x - 1 := by
  have hoff : ∀ y, y ∉ A → u A y = 0 := fun y hy => u_eq_zero_of_notMem A hy
  have hkey := sum_adj_eq_sum_dir A (u A) hoff x
  have hfil : A.filter (fun y => Adj y x) = A.filter (fun y => Adj x y) := by
    refine Finset.filter_congr ?_
    intro y _
    exact ⟨fun h => (adj_comm y x).mp h, fun h => (adj_comm x y).mp h⟩
  unfold ORRW.h
  rw [hfil, hkey]
  ring

/-! ### The numerator of the drift, case by case -/

/-- The numerator of `eq:drift`, as a function of the last letter. -/
private lemma drift_summand (β : ℝ) (v : Fin m → Dir d) (a : Dir d) :
    (Gamma β (Fin.snoc v a) (m + 1) - Gamma β (Fin.snoc v a) m)
        - (Phi (Fin.snoc v a) (m + 1) - Phi (Fin.snoc v a) m)
      = eta (Fin.snoc v a) (m + 1)
            * (gamma β (Fin.snoc v a) m + Phi (Fin.snoc v a) (m + 1))
          - Phi (Fin.snoc v a) (m + 1) + Phi (Fin.snoc v a) m := by
  show (Gamma β (Fin.snoc v a) m
          + eta (Fin.snoc v a) (m + 1)
            * (gamma β (Fin.snoc v a) m + Phi (Fin.snoc v a) (m + 1))
        - Gamma β (Fin.snoc v a) m) - _ = _
  ring

/-- `orrw.tex`, the case `X_m ∈ S_m`: the drift numerator is exactly
`2dβ`, which is `μ_m`, so the drift is exactly `1`. -/
lemma drift_num_saturated (hd : 0 < d) (β : ℝ) (v : Fin m → Dir d) (h0 : nu v m = 0) :
    (∑ a : Dir d, stepWeight β v m a *
        ((Gamma β (Fin.snoc v a) (m + 1) - Gamma β (Fin.snoc v a) m)
          - (Phi (Fin.snoc v a) (m + 1) - Phi (Fin.snoc v a) m)))
      = 2 * (d : ℝ) * β := by
  have hx : pos v m ∈ S v m := (nu_eq_zero_iff hd v m).mp h0
  have hterm : ∀ a : Dir d, stepWeight β v m a *
      ((Gamma β (Fin.snoc v a) (m + 1) - Gamma β (Fin.snoc v a) m)
        - (Phi (Fin.snoc v a) (m + 1) - Phi (Fin.snoc v a) m))
      = β * (2 * (d : ℝ) * u (S v m) (pos v m)
              - 2 * (d : ℝ) * u (S v m) (pos v m + dirVec a)) := by
    intro a
    have ha : s(pos v m, pos v m + dirVec a) ∈ E v m := traversed_of_nu_zero v h0 a
    have hw : stepWeight β v m a = β := by
      unfold stepWeight
      rw [if_pos ha]
    have hE1 : E (Fin.snoc v a) (m + 1) = E v m := E_snoc_succ_of_mem v a ha
    have hS1 : S (Fin.snoc v a) (m + 1) = S v m := S_eq_of_E_eq hd _ _ hE1
    have hP1 : Phi (Fin.snoc v a) (m + 1) = 2 * (d : ℝ) * u (S v m) (pos v m + dirVec a) := by
      unfold Phi
      rw [hS1, pos_snoc_last v a]
    have hP0 : Phi (Fin.snoc v a) m = 2 * (d : ℝ) * u (S v m) (pos v m) := by
      rw [Phi_snoc hd v a (le_refl m)]
      rfl
    rw [drift_summand, eta_snoc_of_mem v a ha, hw, hP1, hP0]
    ring
  have hterm' : ∀ a : Dir d, stepWeight β v m a *
      ((Gamma β (Fin.snoc v a) (m + 1) - Gamma β (Fin.snoc v a) m)
        - (Phi (Fin.snoc v a) (m + 1) - Phi (Fin.snoc v a) m))
      = β * (2 * (d : ℝ) * u (S v m) (pos v m))
        - (β * (2 * (d : ℝ))) * u (S v m) (pos v m + dirVec a) := by
    intro a
    rw [hterm a]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hterm' a), Finset.sum_sub_distrib,
    Finset.sum_const, ← Finset.mul_sum, card_dir,
    ORRW.Support.u_lap hd (S v m) (pos v m) hx, nsmul_eq_mul]
  push_cast
  ring

/-- `orrw.tex`, the case `X_m ∉ S_m`: the drift numerator is
`2dβ(h(ν - 1) + 1)`. -/
lemma drift_num_unsaturated (hd : 0 < d) (β : ℝ) (v : Fin m → Dir d) (h0 : nu v m ≠ 0) :
    (∑ a : Dir d, stepWeight β v m a *
        ((Gamma β (Fin.snoc v a) (m + 1) - Gamma β (Fin.snoc v a) m)
          - (Phi (Fin.snoc v a) (m + 1) - Phi (Fin.snoc v a) m)))
      = 2 * (d : ℝ) * β
          * (ORRW.h (S v m) (pos v m) * ((nu v m : ℝ) - 1) + 1) := by
  classical
  set A := S v m with hA
  set x := pos v m with hxdef
  -- `Φ_m = 0`, `orrw.tex`.
  have hxA : x ∉ A := fun hc => h0 ((nu_eq_zero_iff hd v m).mpr hc)
  have hux : u A x = 0 := u_eq_zero_of_notMem A hxA
  have hPhi0 : Phi v m = 0 := by unfold Phi; rw [← hA, ← hxdef, hux]; ring
  have hgam : gamma β v m = 2 * (d : ℝ) * β * ORRW.h A x := by
    unfold gamma
    rw [if_neg h0]
  -- The two kinds of step.
  set P : Dir d → Prop := fun a => s(x, x + dirVec a) ∈ E v m with hP
  have hterm_mem : ∀ a : Dir d, P a →
      stepWeight β v m a *
        ((Gamma β (Fin.snoc v a) (m + 1) - Gamma β (Fin.snoc v a) m)
          - (Phi (Fin.snoc v a) (m + 1) - Phi (Fin.snoc v a) m))
        = -(β * (2 * (d : ℝ) * u A (x + dirVec a))) := by
    intro a ha
    have hw : stepWeight β v m a = β := by unfold stepWeight; rw [if_pos ha]
    have hE1 : E (Fin.snoc v a) (m + 1) = E v m := E_snoc_succ_of_mem v a ha
    have hS1 : S (Fin.snoc v a) (m + 1) = A := S_eq_of_E_eq hd _ _ hE1
    have hP1 : Phi (Fin.snoc v a) (m + 1) = 2 * (d : ℝ) * u A (x + dirVec a) := by
      unfold Phi
      rw [hS1, pos_snoc_last v a]
    have hP0 : Phi (Fin.snoc v a) m = 0 := by rw [Phi_snoc hd v a (le_refl m), hPhi0]
    rw [drift_summand, eta_snoc_of_mem v a ha, hw, hP1, hP0]
    ring
  have hterm_not : ∀ a : Dir d, ¬ P a →
      stepWeight β v m a *
        ((Gamma β (Fin.snoc v a) (m + 1) - Gamma β (Fin.snoc v a) m)
          - (Phi (Fin.snoc v a) (m + 1) - Phi (Fin.snoc v a) m))
        = 2 * (d : ℝ) * β * ORRW.h A x := by
    intro a ha
    have hw : stepWeight β v m a = 1 := by unfold stepWeight; rw [if_neg ha]
    have hP0 : Phi (Fin.snoc v a) m = 0 := by rw [Phi_snoc hd v a (le_refl m), hPhi0]
    rw [drift_summand, eta_snoc_of_notMem v a ha, hw, hP0,
      gamma_snoc hd β v a (le_refl m), hgam]
    ring
  -- The untraversed directions contribute nothing to `∑ u_A`.
  have hzero : ∀ a : Dir d, ¬ P a → u A (x + dirVec a) = 0 := by
    intro a ha
    exact u_eq_zero_of_notMem A (notMem_S_of_untraversed hd v a ha)
  have hcard : (Finset.univ.filter (fun a : Dir d => ¬ P a)).card = nu v m := by
    unfold nu
    rfl
  have hterm_mem' : ∀ a : Dir d, P a →
      stepWeight β v m a *
        ((Gamma β (Fin.snoc v a) (m + 1) - Gamma β (Fin.snoc v a) m)
          - (Phi (Fin.snoc v a) (m + 1) - Phi (Fin.snoc v a) m))
        = (-(β * (2 * (d : ℝ)))) * u A (x + dirVec a) := by
    intro a ha
    rw [hterm_mem a ha]
    ring
  have hsplit : ∑ a ∈ Finset.univ.filter P, u A (x + dirVec a)
      = ORRW.h A x - 1 := by
    have hall := sum_u_nbr A x
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P
      (fun a => u A (x + dirVec a))] at hall
    have hz : ∑ a ∈ Finset.univ.filter (fun a : Dir d => ¬ P a), u A (x + dirVec a) = 0 :=
      Finset.sum_eq_zero fun a ha => hzero a (Finset.mem_filter.mp ha).2
    rw [hz, add_zero] at hall
    exact hall
  -- Split the sum.
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P]
  rw [Finset.sum_congr rfl (fun a ha => hterm_mem' a (Finset.mem_filter.mp ha).2),
    Finset.sum_congr rfl (fun a ha => hterm_not a (Finset.mem_filter.mp ha).2)]
  rw [← Finset.mul_sum, hsplit, Finset.sum_const, hcard, nsmul_eq_mul]
  ring

/-! ### The drift bound -/

/-- `eq:drift` of `orrw.tex`, the assertion of `lem:martingale`. -/
theorem drift_ge_one (hd : 1 ≤ d) {β : ℝ} (hβ : 1 ≤ β) (m : ℕ) (v : Fin m → Dir d) :
    1 ≤ (∑ a : Dir d, stepWeight β v m a *
            ((Gamma β (Fin.snoc v a) (m + 1) - Gamma β (Fin.snoc v a) m)
              - (Phi (Fin.snoc v a) (m + 1) - Phi (Fin.snoc v a) m)))
          / mu β v m := by
  have hd0 : 0 < d := hd
  have hmupos : 0 < mu β v m := mu_pos hd0 hβ v m
  rw [le_div_iff₀ hmupos, one_mul]
  by_cases h0 : nu v m = 0
  · rw [drift_num_saturated hd0 β v h0]
    unfold mu
    rw [h0]
    push_cast
    ring_nf
    linarith
  · rw [drift_num_unsaturated hd0 β v h0]
    have hh : 1 ≤ ORRW.h (S v m) (pos v m) := ORRW.Support.one_le_h hd0 _ _
    have hnu : (1 : ℝ) ≤ (nu v m : ℝ) := by
      have : 1 ≤ nu v m := Nat.one_le_iff_ne_zero.mpr h0
      exact_mod_cast this
    have hdb : (0 : ℝ) < 2 * (d : ℝ) * β := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
      nlinarith
    have hprod : 0 ≤ ORRW.h (S v m) (pos v m) * ((nu v m : ℝ) - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have hstep : 0 ≤ 2 * (d : ℝ) * β * (ORRW.h (S v m) (pos v m) * ((nu v m : ℝ) - 1)) :=
      mul_nonneg (le_of_lt hdb) hprod
    nlinarith [mu_le hβ v m, hstep]

end ORRW.Support
