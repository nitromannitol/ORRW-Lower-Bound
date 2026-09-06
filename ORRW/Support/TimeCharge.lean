/-
Supporting lemmas for `ORRW.Frozen.time_versus_charge` (`lem:exp`,
`orrw.tex`).

The proof of that lemma is the paper's own: with `θ = [4(1+p+q)]^{-1}` and
`δ_n := Γ_{(n+1)∧ζ} - Γ_{n∧ζ}`,

  `Z_n := e^{θ(n∧ζ)/2 - 2θΓ_{n∧ζ}}(1 + θΦ_{n∧ζ})`

is a nonnegative supermartingale with `Z_0 = 1`.  Under ruling R-001 there is no
measure theory: "supermartingale" is the inequality `E Z_{n+1} ≤ E Z_n` between
two `Finset` sums over the word space, and it follows from a single pointwise
one-step estimate against the step rule of `ORRW/Basic.lean`, which is
`timeCharge_step_core` below.  Nothing in this file is frozen.
-/
import ORRW.Potential
import ORRW.Support.Return

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

/-- Bounds the elementary inequality e^{-2x} ≤ 1 - x for x in [0, 1/2], used in the one-step supermartingale estimate. -/
theorem exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have hpos : (0 : ℝ) < Real.exp (2 * x) := Real.exp_pos _
  have h1 : 1 + 2 * x ≤ Real.exp (2 * x) := by
    have := Real.add_one_le_exp (2 * x); linarith
  have hkey : 1 ≤ (1 - x) * Real.exp (2 * x) := by nlinarith
  have hmul : Real.exp (-(2 * x)) * Real.exp (2 * x) = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [hpos]

/-- The one-step estimate behind the supermartingale argument: it rewrites the expected value after the next step as a finite sum over sites of the transition probability times the function value, which is what makes the pointwise comparison against the step rule possible. -/
theorem expect_succ {d m : ℕ} (β : ℝ) (f : (Fin (m + 1) → Dir d) → ℝ) :
    expect (m + 1) β f
      = ∑ v : Fin m → Dir d, prob β v *
          ((∑ a : Dir d, stepWeight β v m a * f (Fin.snoc v a)) / totalWeight β v m) := by
  have hre : ∑ w : Fin (m + 1) → Dir d, prob β w * f w
      = ∑ p : Dir d × (Fin m → Dir d), prob β (Fin.snoc p.2 p.1) * f (Fin.snoc p.2 p.1) :=
    (Fintype.sum_equiv (Fin.snocEquiv (fun _ => Dir d))
      (fun p => prob β (Fin.snoc p.2 p.1) * f (Fin.snoc p.2 p.1))
      (fun w => prob β w * f w) (fun _ => rfl)).symm
  unfold expect
  rw [hre, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hstep : ∀ a : Dir d, prob β (Fin.snoc v a)
      = prob β v * (stepWeight β v m a / totalWeight β v m) := by
    intro a
    rw [prob_succ β (Fin.snoc v a), Fin.init_snoc, Fin.snoc_last]
  have hterm : ∀ a : Dir d, prob β (Fin.snoc v a) * f (Fin.snoc v a)
      = prob β v * ((stepWeight β v m a * f (Fin.snoc v a)) / totalWeight β v m) := by
    intro a; rw [hstep a]; ring
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.mul_sum, ← Finset.sum_div]

/-- Pointwise one-step estimate feeding the supermartingale inequality: the expected value of the potential after appending a direction, weighted by the step rule, is bounded by the charge at the current site. -/
theorem expect_succ_le {d m : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β)
    (f : (Fin (m + 1) → Dir d) → ℝ) (g : (Fin m → Dir d) → ℝ)
    (h : ∀ v : Fin m → Dir d,
        (∑ a : Dir d, stepWeight β v m a * f (Fin.snoc v a)) / totalWeight β v m ≤ g v) :
    expect (m + 1) β f ≤ expect m β g := by
  rw [expect_succ β f]
  refine Finset.sum_le_sum fun v _ => ?_
  exact mul_le_mul_of_nonneg_left (h v) (prob_pos hd hβ v).le

/-- Supplies the pointwise one-step estimate behind the supermartingale argument, bounding the expected exponential drop in charge at a site by the drift in potential so the frozen-time-versus-charge comparison can proceed. -/
theorem timeCharge_step_core {ι : Type*} [Fintype ι] (P : ι → ℝ)
    (hP0 : ∀ i, 0 ≤ P i) (hP1 : ∑ i, P i = 1)
    (θ p q : ℝ) (hθpos : 0 < θ) (hθp : θ * p ≤ 1 / 4) (hθq : θ * q ≤ 1 / 4)
    (Φm : ℝ) (hΦm0 : 0 ≤ Φm) (hΦmp : Φm ≤ p)
    (Φ' δ : ι → ℝ) (hΦ'0 : ∀ i, 0 ≤ Φ' i) (hδ0 : ∀ i, 0 ≤ δ i) (hδq : ∀ i, δ i ≤ q)
    (c : ℝ) (hc0 : 0 ≤ c)
    (hdr : c ≤ ∑ i, P i * (δ i - (Φ' i - Φm))) :
    Real.exp (θ * c / 2) * ∑ i, P i * (Real.exp (-(2 * θ * δ i)) * (1 + θ * Φ' i))
      ≤ 1 + θ * Φm := by
  have hθΦm : θ * Φm ≤ 1 / 4 := le_trans (by nlinarith) hθp
  have hΦmnn : (0 : ℝ) ≤ 1 + θ * Φm := by nlinarith
  have h1 : ∀ i, P i * (Real.exp (-(2 * θ * δ i)) * (1 + θ * Φ' i))
      ≤ P i * (1 + θ * Φ' i - θ * δ i) := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (hP0 i)
    have hd0 : 0 ≤ θ * δ i := mul_nonneg hθpos.le (hδ0 i)
    have hd1 : θ * δ i ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_left (hδq i) hθpos.le]
    have he : Real.exp (-(2 * (θ * δ i))) ≤ 1 - θ * δ i := exp_neg_two_mul_le_one_sub hd0 hd1
    have hnn : (0 : ℝ) ≤ 1 + θ * Φ' i := by nlinarith [hΦ'0 i, mul_nonneg hθpos.le (hΦ'0 i)]
    have hrw : -(2 * θ * δ i) = -(2 * (θ * δ i)) := by ring
    rw [hrw]
    nlinarith [mul_le_mul_of_nonneg_right he hnn,
      mul_nonneg (mul_nonneg hθpos.le (hδ0 i)) (mul_nonneg hθpos.le (hΦ'0 i))]
  have hexp : ∑ i, P i * (1 + θ * Φ' i - θ * δ i)
      = (∑ i, P i) + θ * ∑ i, P i * (Φ' i - δ i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hdr' : ∑ i, P i * (δ i - (Φ' i - Φm)) = (∑ i, P i * (δ i - Φ' i)) + Φm := by
    have hh : ∀ i, P i * (δ i - (Φ' i - Φm)) = P i * (δ i - Φ' i) + Φm * P i :=
      fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => hh i, Finset.sum_add_distrib, ← Finset.mul_sum, hP1,
      mul_one]
  have hsum0 : (∑ i, P i * (Φ' i - δ i)) + (∑ i, P i * (δ i - Φ' i)) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring
  have hX : ∑ i, P i * (Φ' i - δ i) ≤ Φm - c := by linarith
  have h2 : ∑ i, P i * (1 + θ * Φ' i - θ * δ i) ≤ 1 + θ * Φm - θ * c := by
    have := mul_le_mul_of_nonneg_left hX hθpos.le
    rw [hexp, hP1]; linarith
  have h3 : 1 + θ * Φm - θ * c ≤ Real.exp (-(θ * c / 2)) * (1 + θ * Φm) := by
    have hc : 0 ≤ θ * c := mul_nonneg hθpos.le hc0
    have hexpn := Real.one_sub_le_exp_neg (θ * c / 2)
    nlinarith [mul_le_mul_of_nonneg_right hexpn hΦmnn,
      mul_nonneg hc (by linarith : (0 : ℝ) ≤ 1 - θ * Φm)]
  have h4 : ∑ i, P i * (Real.exp (-(2 * θ * δ i)) * (1 + θ * Φ' i))
      ≤ Real.exp (-(θ * c / 2)) * (1 + θ * Φm) :=
    le_trans (le_trans (Finset.sum_le_sum fun i _ => h1 i) h2) h3
  calc Real.exp (θ * c / 2) * ∑ i, P i * (Real.exp (-(2 * θ * δ i)) * (1 + θ * Φ' i))
      ≤ Real.exp (θ * c / 2) * (Real.exp (-(θ * c / 2)) * (1 + θ * Φm)) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = 1 + θ * Φm := by rw [← mul_assoc, ← Real.exp_add]; simp

/-- The supermartingale `Z_n = e^{θ(n∧ζ)/2 - 2θΓ_{n∧ζ}}(1 + θΦ_{n∧ζ})` has mean at most one. -/
theorem timeCharge_supermartingale {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β)
    (Φ Γ : ∀ m : ℕ, (Fin m → Dir d) → ℝ)
    (ζ χ : ∀ m : ℕ, (Fin m → Dir d) → ℕ)
    (p q θ : ℝ) (hθpos : 0 < θ) (hθp : θ * p ≤ 1 / 4) (hθq : θ * q ≤ 1 / 4)
    (hζ0 : ∀ v : Fin 0 → Dir d, ζ 0 v = 0)
    (hΦ0 : ∀ v : Fin 0 → Dir d, Φ 0 v = 0)
    (hΓ0 : ∀ v : Fin 0 → Dir d, Γ 0 v = 0)
    (hζ : ∀ (m : ℕ) (v : Fin m → Dir d) (a : Dir d),
        ζ (m + 1) (Fin.snoc v a) = ζ m v + χ m v)
    (hΦ : ∀ (m : ℕ) (v : Fin m → Dir d), 0 ≤ Φ m v ∧ Φ m v ≤ p)
    (hδ : ∀ (m : ℕ) (v : Fin m → Dir d) (a : Dir d),
        0 ≤ Γ (m + 1) (Fin.snoc v a) - Γ m v ∧ Γ (m + 1) (Fin.snoc v a) - Γ m v ≤ q)
    (hdrift : ∀ (m : ℕ) (v : Fin m → Dir d),
        (χ m v : ℝ) ≤ (∑ a : Dir d, stepWeight β v m a *
              ((Γ (m + 1) (Fin.snoc v a) - Γ m v) - (Φ (m + 1) (Fin.snoc v a) - Φ m v)))
            / mu β v m) (N : ℕ) :
    expect N β (fun w => Real.exp (θ * (ζ N w : ℝ) / 2 - 2 * θ * Γ N w) * (1 + θ * Φ N w))
      ≤ 1 := by
  induction N with
  | zero =>
      have hterm : ∀ w : Fin 0 → Dir d,
          prob β w * (Real.exp (θ * (ζ 0 w : ℝ) / 2 - 2 * θ * Γ 0 w) * (1 + θ * Φ 0 w))
            = prob β w := by
        intro w
        rw [hζ0 w, hΓ0 w, hΦ0 w]
        norm_num
      unfold expect
      rw [Finset.sum_congr rfl fun w _ => hterm w, sum_prob_eq_one hd hβ 0]
  | succ m ih =>
      refine le_trans ?_ ih
      refine expect_succ_le hd hβ _ _ ?_
      intro v
      have htwpos : 0 < totalWeight β v m := totalWeight_pos hd hβ v m
      have hmu : mu β v m = totalWeight β v m := mu_eq_totalWeight β v m
      have hP0 : ∀ a : Dir d, 0 ≤ stepWeight β v m a / totalWeight β v m := fun a =>
        le_of_lt (div_pos (stepWeight_pos hβ v m a) htwpos)
      have hP1 : ∑ a : Dir d, stepWeight β v m a / totalWeight β v m = 1 := by
        rw [← Finset.sum_div]
        exact div_self htwpos.ne'
      have hdr : (χ m v : ℝ) ≤ ∑ a : Dir d, (stepWeight β v m a / totalWeight β v m) *
          ((Γ (m + 1) (Fin.snoc v a) - Γ m v) - (Φ (m + 1) (Fin.snoc v a) - Φ m v)) := by
        have hh := hdrift m v
        rw [hmu, Finset.sum_div] at hh
        refine le_trans hh (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
        ring
      have hsum : (∑ a : Dir d, stepWeight β v m a *
              (Real.exp (θ * (ζ (m + 1) (Fin.snoc v a) : ℝ) / 2 - 2 * θ * Γ (m + 1) (Fin.snoc v a))
                * (1 + θ * Φ (m + 1) (Fin.snoc v a)))) / totalWeight β v m
          = Real.exp (θ * (ζ m v : ℝ) / 2 - 2 * θ * Γ m v) *
              (Real.exp (θ * (χ m v : ℝ) / 2) *
                ∑ a : Dir d, (stepWeight β v m a / totalWeight β v m) *
                  (Real.exp (-(2 * θ * (Γ (m + 1) (Fin.snoc v a) - Γ m v)))
                    * (1 + θ * Φ (m + 1) (Fin.snoc v a)))) := by
        rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hζ m v a]
        push_cast
        have hsplit : θ * ((ζ m v : ℝ) + (χ m v : ℝ)) / 2 - 2 * θ * Γ (m + 1) (Fin.snoc v a)
            = (θ * (ζ m v : ℝ) / 2 - 2 * θ * Γ m v) + θ * (χ m v : ℝ) / 2
              + -(2 * θ * (Γ (m + 1) (Fin.snoc v a) - Γ m v)) := by ring
        rw [hsplit, Real.exp_add, Real.exp_add]
        ring
      show (∑ a : Dir d, stepWeight β v m a *
              (Real.exp (θ * (ζ (m + 1) (Fin.snoc v a) : ℝ) / 2 - 2 * θ * Γ (m + 1) (Fin.snoc v a))
                * (1 + θ * Φ (m + 1) (Fin.snoc v a)))) / totalWeight β v m
          ≤ Real.exp (θ * (ζ m v : ℝ) / 2 - 2 * θ * Γ m v) * (1 + θ * Φ m v)
      rw [hsum]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact timeCharge_step_core (fun a => stepWeight β v m a / totalWeight β v m) hP0 hP1
        θ p q hθpos hθp hθq (Φ m v) (hΦ m v).1 (hΦ m v).2
        (fun a => Φ (m + 1) (Fin.snoc v a)) (fun a => Γ (m + 1) (Fin.snoc v a) - Γ m v)
        (fun a => (hΦ (m + 1) (Fin.snoc v a)).1) (fun a => (hδ m v a).1) (fun a => (hδ m v a).2)
        ((χ m v : ℝ)) (Nat.cast_nonneg _) hdr

/-- Markov's inequality in the form used by `lem:exp`. -/
theorem prb_le_exp_of_expect_exp {d N : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β)
    (g : (Fin N → Dir d) → ℝ) (t M : ℝ)
    (hM : expect N β (fun w => Real.exp (g w)) ≤ Real.exp M)
    (P : (Fin N → Dir d) → Prop) (hP : ∀ w, P w → t ≤ g w) :
    prb N β P ≤ Real.exp (M - t) := by
  classical
  have hkey : Real.exp t * prb N β P ≤ expect N β (fun w => Real.exp (g w)) := by
    unfold prb expect
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    by_cases h : P w
    · rw [if_pos h]
      have h2 : Real.exp t ≤ Real.exp (g w) := Real.exp_le_exp.mpr (hP w h)
      calc Real.exp t * (prob β w * 1) = prob β w * Real.exp t := by ring
        _ ≤ prob β w * Real.exp (g w) := mul_le_mul_of_nonneg_left h2 (prob_pos hd hβ w).le
    · rw [if_neg h]
      have hz : Real.exp t * (prob β w * 0) = 0 := by ring
      rw [hz]
      exact mul_nonneg (prob_pos hd hβ w).le (Real.exp_nonneg _)
  have hfin : Real.exp t * prb N β P ≤ Real.exp M := le_trans hkey hM
  have hEq : Real.exp t * Real.exp (M - t) = Real.exp M := by
    rw [← Real.exp_add]; congr 1; ring
  exact le_of_mul_le_mul_left (by rw [hEq]; exact hfin) (Real.exp_pos t)

/-- The exponential moment bound of `lem:exp`. -/
theorem timeCharge_mgf {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β)
    (Φ Γ : ∀ m : ℕ, (Fin m → Dir d) → ℝ)
    (ζ χ : ∀ m : ℕ, (Fin m → Dir d) → ℕ)
    (p q b θ : ℝ) (hθpos : 0 < θ) (hθp : θ * p ≤ 1 / 4) (hθq : θ * q ≤ 1 / 4)
    (hζ0 : ∀ v : Fin 0 → Dir d, ζ 0 v = 0)
    (hΦ0 : ∀ v : Fin 0 → Dir d, Φ 0 v = 0)
    (hΓ0 : ∀ v : Fin 0 → Dir d, Γ 0 v = 0)
    (hζ : ∀ (m : ℕ) (v : Fin m → Dir d) (a : Dir d),
        ζ (m + 1) (Fin.snoc v a) = ζ m v + χ m v)
    (hΦ : ∀ (m : ℕ) (v : Fin m → Dir d), 0 ≤ Φ m v ∧ Φ m v ≤ p)
    (hδ : ∀ (m : ℕ) (v : Fin m → Dir d) (a : Dir d),
        0 ≤ Γ (m + 1) (Fin.snoc v a) - Γ m v ∧ Γ (m + 1) (Fin.snoc v a) - Γ m v ≤ q)
    (hΓ : ∀ (m : ℕ) (v : Fin m → Dir d), Γ m v ≤ b)
    (hdrift : ∀ (m : ℕ) (v : Fin m → Dir d),
        (χ m v : ℝ) ≤ (∑ a : Dir d, stepWeight β v m a *
              ((Γ (m + 1) (Fin.snoc v a) - Γ m v) - (Φ (m + 1) (Fin.snoc v a) - Φ m v)))
            / mu β v m) (N : ℕ) :
    expect N β (fun w => Real.exp (θ * (ζ N w : ℝ) / 2)) ≤ Real.exp (2 * θ * b) := by
  have hsm := timeCharge_supermartingale hd hβ Φ Γ ζ χ p q θ hθpos hθp hθq hζ0 hΦ0 hΓ0 hζ hΦ hδ
    hdrift N
  have hle : ∀ w : Fin N → Dir d,
      Real.exp (-(2 * θ * b)) * Real.exp (θ * (ζ N w : ℝ) / 2)
        ≤ Real.exp (θ * (ζ N w : ℝ) / 2 - 2 * θ * Γ N w) * (1 + θ * Φ N w) := by
    intro w
    have h1 : Real.exp (-(2 * θ * b)) * Real.exp (θ * (ζ N w : ℝ) / 2)
        = Real.exp (θ * (ζ N w : ℝ) / 2 - 2 * θ * b) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (θ * (ζ N w : ℝ) / 2 - 2 * θ * b)
        ≤ Real.exp (θ * (ζ N w : ℝ) / 2 - 2 * θ * Γ N w) :=
      Real.exp_le_exp.mpr (by nlinarith [hΓ N w])
    have h3 : (1 : ℝ) ≤ 1 + θ * Φ N w := by nlinarith [mul_nonneg hθpos.le (hΦ N w).1]
    rw [h1]
    calc Real.exp (θ * (ζ N w : ℝ) / 2 - 2 * θ * b)
        ≤ Real.exp (θ * (ζ N w : ℝ) / 2 - 2 * θ * Γ N w) := h2
      _ = Real.exp (θ * (ζ N w : ℝ) / 2 - 2 * θ * Γ N w) * 1 := by ring
      _ ≤ Real.exp (θ * (ζ N w : ℝ) / 2 - 2 * θ * Γ N w) * (1 + θ * Φ N w) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
  have hstep : Real.exp (-(2 * θ * b)) * expect N β (fun w => Real.exp (θ * (ζ N w : ℝ) / 2))
      ≤ expect N β (fun w => Real.exp (θ * (ζ N w : ℝ) / 2 - 2 * θ * Γ N w) * (1 + θ * Φ N w)) := by
    unfold expect
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    have hre : Real.exp (-(2 * θ * b)) * (prob β w * Real.exp (θ * (ζ N w : ℝ) / 2))
        = prob β w * (Real.exp (-(2 * θ * b)) * Real.exp (θ * (ζ N w : ℝ) / 2)) := by ring
    rw [hre]
    exact mul_le_mul_of_nonneg_left (hle w) (prob_pos hd hβ w).le
  have hfin : Real.exp (-(2 * θ * b)) * expect N β (fun w => Real.exp (θ * (ζ N w : ℝ) / 2))
      ≤ 1 := le_trans hstep hsm
  have hb : Real.exp (-(2 * θ * b)) * Real.exp (2 * θ * b) = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (-(2 * θ * b))]

end ORRW
