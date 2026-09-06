/-
Supporting lemmas for the insertion inequality of Bou-Rabee--Peres, Section 2,
`orrw.tex` (label `lem:insertion`).

Nothing here is frozen.  `insertion_inequality_of` is the paper's argument with
its two external inputs -- the exit time bounds `lem:max-exit` and the
resistance packing bound `lem:packing` -- taken as explicit hypotheses, so that
this file is unconditional and the dependency on those two nodes is visible at
the single point where the frozen statement is discharged.

The argument: `pref x k` is the set of the first `k` inserted sites, so that
the paper's `A_{i-1}` is `pref x i` and its `A_i` is `pref x (i+1)`.
`one_point_insertion` gives, at each step, `u = Reff * h` and
`T(A_i) - T(A_{i-1}) = h * u`, hence `h^2 <= 2d (T(A_i) - T(A_{i-1}))` from
`Reff >= 1/(2d)`, and `u^2 = Reff (T(A_i) - T(A_{i-1}))`.  Summing the
telescoping differences gives `T(A_M)`, and two Cauchy--Schwarz inequalities
turn the two families into `M^{1+1/d}`.
-/
import Mathlib
import ORRW.Basic
import ORRW.Lattice
import ORRW.Support.Insertion

open Finset
open scoped Matrix

namespace ORRW.Support

variable {d : ℕ}

/-- The prefix sets of an insertion order, indexed by `ℕ`. -/
def pref {M : ℕ} (x : Fin M → Site d) (k : ℕ) : Finset (Site d) :=
  (Finset.univ.filter (fun j : Fin M => (j : ℕ) < k)).image x

/-- Identifies the empty prefix of inserted sites before any step, anchoring the telescoping of exit times over the insertion sequence. -/
lemma pref_zero {M : ℕ} (x : Fin M → Site d) : pref x 0 = ∅ := by
  simp [pref]

/-- Identifies the first `i` inserted sites as a prefix of the walk's site sequence, so the paper's sets `A_{i-1}` and `A_i` can be read off directly when the insertion inequality is proved step by step. -/
lemma pref_Iio {M : ℕ} (x : Fin M → Site d) (i : Fin M) :
    (Finset.Iio i).image x = pref x (i : ℕ) := by
  congr 1
  ext j
  simp only [Finset.mem_Iio, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Fin.lt_def

/-- Identifies the set of the first i+1 inserted sites as the prefix of length i+1, matching the paper's A_i in the insertion inequality argument. -/
lemma pref_succ {M : ℕ} (x : Fin M → Site d) (i : Fin M) :
    insert (x i) (pref x (i : ℕ)) = pref x ((i : ℕ) + 1) := by
  ext y
  simp only [pref, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨j, by omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    rcases Nat.lt_or_ge (j : ℕ) (i : ℕ) with hji | hji
    · exact Or.inr ⟨j, hji, rfl⟩
    · left
      congr 1
      exact Fin.ext (by omega)

/-- The prefix of inserted sites is monotone, so the sets `A_i` used in the insertion inequality form an increasing chain. -/
lemma pref_mono {M : ℕ} (x : Fin M → Site d) {k l : ℕ} (h : k ≤ l) :
    pref x k ⊆ pref x l := by
  intro y hy
  simp only [pref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  obtain ⟨j, hj, rfl⟩ := hy
  exact ⟨j, by omega, rfl⟩

/-- No site appears twice in the inserted sequence, so each prefix of inserted sites has exactly as many points as its length. -/
lemma pref_notMem {M : ℕ} (x : Fin M → Site d) (hinj : Function.Injective x) (i : Fin M) :
    x i ∉ pref x (i : ℕ) := by
  simp only [pref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨j, hj, hxj⟩
  have : j = i := hinj hxj
  omega

/-- The first k inserted sites form a set of exactly k distinct points, so the prefix used as A_{i-1} in the insertion inequality has the right cardinality. -/
lemma pref_card {M : ℕ} (x : Fin M → Site d) (hinj : Function.Injective x) :
    (pref x M).card = M := by
  have huniv : (Finset.univ.filter (fun j : Fin M => (j : ℕ) < M)) = Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact j.2
  rw [pref, huniv, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- The insertion inequality of `lem:insertion`, given the exit time bounds of
`lem:max-exit` and the resistance packing bound of `lem:packing`. -/
theorem insertion_inequality_of (hd : 2 ≤ d)
    (hmax : ∃ C : ℝ, 0 < C ∧ ∀ A : Finset (Site d), A.Nonempty →
      (∀ y ∈ A, u A y ≤ C * (A.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ∧
      (∀ y ∉ A, ORRW.h A y ≤ C * (A.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ∧
      T A ≤ C * (A.card : ℝ) ^ (1 + (2 : ℝ) / (d : ℝ)))
    (hpack : ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → ∀ x : Fin M → Site d, Function.Injective x →
      ∑ i : Fin M, Reff ((Finset.Iio i).image x) (x i) ≤ C * (M : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → ∀ x : Fin M → Site d, Function.Injective x →
      ∑ i : Fin M, (ORRW.h ((Finset.Iio i).image x) (x i)
            + u (insert (x i) ((Finset.Iio i).image x)) (x i))
        ≤ C * (M : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) := by
  classical
  obtain ⟨C₁, hC₁, hmax'⟩ := hmax
  obtain ⟨C₂, hC₂, hpack'⟩ := hpack
  have hd1 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
  refine ⟨Real.sqrt (2*(d:ℝ)*C₁) + Real.sqrt (C₁*C₂), by positivity, ?_⟩
  intro M hM x hinj
  simp only [pref_Iio]
  set P : ℝ := (M:ℝ) ^ (1 + (1:ℝ)/(d:ℝ)) with hP
  have hMR : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hPpos : 0 < P := Real.rpow_pos_of_pos hMR _
  have hPP : P * P = (M:ℝ) * (M:ℝ) ^ (1 + (2:ℝ)/(d:ℝ)) := by
    have h1 : P * P = (M:ℝ) ^ ((1 + (1:ℝ)/(d:ℝ)) + (1 + (1:ℝ)/(d:ℝ))) :=
      (Real.rpow_add hMR _ _).symm
    have h2 : (M:ℝ) * (M:ℝ) ^ (1 + (2:ℝ)/(d:ℝ)) = (M:ℝ) ^ ((1:ℝ) + (1 + (2:ℝ)/(d:ℝ))) := by
      rw [Real.rpow_add hMR (1:ℝ) (1 + (2:ℝ)/(d:ℝ)), Real.rpow_one]
    rw [h1, h2]
    congr 1
    ring
  have key : ∀ i : Fin M,
      u (insert (x i) (pref x (i:ℕ))) (x i)
          = Reff (pref x (i:ℕ)) (x i) * ORRW.h (pref x (i:ℕ)) (x i)
      ∧ T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))
          = ORRW.h (pref x (i:ℕ)) (x i) * u (insert (x i) (pref x (i:ℕ))) (x i)
      ∧ 1/(2*(d:ℝ)) ≤ Reff (pref x (i:ℕ)) (x i) := by
    intro i
    obtain ⟨e1, e2, e3⟩ :=
      one_point_insertion hd1 (pref x (i:ℕ)) (x i) (pref_notMem x hinj i)
    refine ⟨e1, ?_, e3⟩
    rw [← pref_succ x i]
    exact e2
  have hRnn : ∀ i : Fin M, 0 ≤ Reff (pref x (i:ℕ)) (x i) := by
    intro i
    exact le_trans (by positivity) (key i).2.2
  have hdTnn : ∀ i : Fin M, 0 ≤ T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ)) := by
    intro i
    obtain ⟨e1, e2, _⟩ := key i
    rw [e2, e1]
    have hh0 : (0:ℝ) ≤ ORRW.h (pref x (i:ℕ)) (x i) :=
      le_trans zero_le_one (one_le_h hd1 _ _)
    exact mul_nonneg hh0 (mul_nonneg (hRnn i) hh0)
  have hhsq : ∀ i : Fin M, (ORRW.h (pref x (i:ℕ)) (x i))^2
      ≤ 2*(d:ℝ)*(T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) := by
    intro i
    obtain ⟨e1, e2, e3⟩ := key i
    rw [e2, e1]
    rw [div_le_iff₀ (by positivity)] at e3
    nlinarith [sq_nonneg (ORRW.h (pref x (i:ℕ)) (x i)), e3]
  have huabs : ∀ i : Fin M, u (insert (x i) (pref x (i:ℕ))) (x i)
      ≤ Real.sqrt (Reff (pref x (i:ℕ)) (x i))
        * Real.sqrt (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) := by
    intro i
    obtain ⟨e1, e2, _⟩ := key i
    have hsq : (u (insert (x i) (pref x (i:ℕ))) (x i))^2
        = Reff (pref x (i:ℕ)) (x i) * (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) := by
      rw [e2, e1]; ring
    calc u (insert (x i) (pref x (i:ℕ))) (x i)
        ≤ |u (insert (x i) (pref x (i:ℕ))) (x i)| := le_abs_self _
      _ = Real.sqrt ((u (insert (x i) (pref x (i:ℕ))) (x i))^2) := (Real.sqrt_sq_eq_abs _).symm
      _ = Real.sqrt (Reff (pref x (i:ℕ)) (x i)
            * (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ)))) := by rw [hsq]
      _ = Real.sqrt (Reff (pref x (i:ℕ)) (x i))
            * Real.sqrt (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) := Real.sqrt_mul (hRnn i) _
  have htel : ∑ i : Fin M, (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) = T (pref x M) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => T (pref x (k+1)) - T (pref x k)) M,
      Finset.sum_range_sub (fun k => T (pref x k)) M, pref_zero]
    simp [T]
  have hTM : T (pref x M) ≤ C₁ * (M:ℝ) ^ (1 + (2:ℝ)/(d:ℝ)) := by
    have hne : (pref x M).Nonempty := by
      rw [← Finset.card_pos, pref_card x hinj]
      omega
    have hb := (hmax' (pref x M) hne).2.2
    rwa [pref_card x hinj] at hb
  have hRsum : ∑ i : Fin M, Reff (pref x (i:ℕ)) (x i) ≤ C₂ * (M:ℝ) := by
    have hb := hpack' M hM x hinj
    simpa only [pref_Iio] using hb
  rw [Finset.sum_add_distrib]
  have hHbound : (∑ i : Fin M, ORRW.h (pref x (i:ℕ)) (x i)) ≤ Real.sqrt (2*(d:ℝ)*C₁) * P := by
    have h1 : (∑ i : Fin M, ORRW.h (pref x (i:ℕ)) (x i))^2
        ≤ (M:ℝ) * ∑ i : Fin M, (ORRW.h (pref x (i:ℕ)) (x i))^2 := by
      have hc := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin M)))
        (f := fun i => ORRW.h (pref x (i:ℕ)) (x i))
      simpa using hc
    have h2 : (∑ i : Fin M, (ORRW.h (pref x (i:ℕ)) (x i))^2) ≤ 2*(d:ℝ)*T (pref x M) := by
      calc (∑ i : Fin M, (ORRW.h (pref x (i:ℕ)) (x i))^2)
          ≤ ∑ i : Fin M, 2*(d:ℝ)*(T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) :=
            Finset.sum_le_sum (fun i _ => hhsq i)
        _ = 2*(d:ℝ) * ∑ i : Fin M, (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) := by
            rw [Finset.mul_sum]
        _ = 2*(d:ℝ)*T (pref x M) := by rw [htel]
    have h3 : (∑ i : Fin M, ORRW.h (pref x (i:ℕ)) (x i))^2 ≤ (2*(d:ℝ)*C₁) * (P*P) := by
      have h4 : (M:ℝ) * ∑ i : Fin M, (ORRW.h (pref x (i:ℕ)) (x i))^2
          ≤ (M:ℝ) * (2*(d:ℝ)*(C₁ * (M:ℝ)^(1+(2:ℝ)/(d:ℝ)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hMR.le
        exact h2.trans (by nlinarith [hTM])
      rw [hPP]
      refine h1.trans (h4.trans ?_)
      ring_nf
      exact le_refl _
    have h5 := Real.sqrt_le_sqrt h3
    rw [Real.sqrt_sq_eq_abs] at h5
    have h6 : Real.sqrt ((2*(d:ℝ)*C₁)*(P*P)) = Real.sqrt (2*(d:ℝ)*C₁) * P := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul_self hPpos.le]
    rw [h6] at h5
    exact le_trans (le_abs_self _) h5
  have hUbound : (∑ i : Fin M, u (insert (x i) (pref x (i:ℕ))) (x i))
      ≤ Real.sqrt (C₁*C₂) * P := by
    have h1 : (∑ i : Fin M, u (insert (x i) (pref x (i:ℕ))) (x i))
        ≤ ∑ i : Fin M, Real.sqrt (Reff (pref x (i:ℕ)) (x i))
            * Real.sqrt (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) :=
      Finset.sum_le_sum (fun i _ => huabs i)
    have h2 := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin M))
      (f := fun i : Fin M => Reff (pref x (i:ℕ)) (x i))
      (g := fun i : Fin M => T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))) hRnn hdTnn
    have h3 : Real.sqrt (∑ i : Fin M, Reff (pref x (i:ℕ)) (x i))
        * Real.sqrt (∑ i : Fin M, (T (pref x ((i:ℕ)+1)) - T (pref x (i:ℕ))))
        ≤ Real.sqrt (C₂ * (M:ℝ)) * Real.sqrt (C₁ * (M:ℝ)^(1+(2:ℝ)/(d:ℝ))) := by
      refine mul_le_mul (Real.sqrt_le_sqrt hRsum) ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      rw [htel]
      exact Real.sqrt_le_sqrt hTM
    have h4 : Real.sqrt (C₂ * (M:ℝ)) * Real.sqrt (C₁ * (M:ℝ)^(1+(2:ℝ)/(d:ℝ)))
        = Real.sqrt (C₁*C₂) * P := by
      rw [← Real.sqrt_mul (by positivity)]
      have h5 : C₂ * (M:ℝ) * (C₁ * (M:ℝ)^(1+(2:ℝ)/(d:ℝ))) = (C₁*C₂) * (P*P) := by
        rw [hPP]; ring
      rw [h5, Real.sqrt_mul (by positivity), Real.sqrt_mul_self hPpos.le]
    linarith [h1, h2, h3, h4 ▸ h3]
  have : Real.sqrt (2*(d:ℝ)*C₁) * P + Real.sqrt (C₁*C₂) * P
      = (Real.sqrt (2*(d:ℝ)*C₁) + Real.sqrt (C₁*C₂)) * P := by ring
  linarith [hHbound, hUbound]

end ORRW.Support
