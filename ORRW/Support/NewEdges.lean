/-
First crossings use distinct edges.

`orrw.tex`: "The steps with `η_{j+1} = 1` cross distinct edges, so the
last sum is at most the total variation of `g_R` over all edges of `Z^d`."  The
total variation is written in the parametrization of ruling F-805, one pair
`(x, i)` per undirected edge.

The file also records that after its first step the walk stands at a site with a
traversed incident edge (`orrw.tex`), which is what bounds
`κ_j = 4dβ/μ_j` above by `4d`.
-/
import Mathlib
import ORRW.LazyWalk
import ORRW.Potential
import ORRW.Support.WalkOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

variable {d : ℕ}

/-- After its first step the walk always stands at a site with a traversed
incident edge. -/
theorem nu_lt (hd : 0 < d) {n : ℕ} (w : Fin n → Dir d) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    nu w j < 2 * d := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : k < n := by omega
  -- the step just taken crossed `edgeAt w k`, so reversing it stays on a traversed edge
  have hstep : pos w (k + 1) = pos w k + dirVec (w ⟨k, hk⟩) := pos_succ w k hk
  have hback : pos w (k + 1) + dirVec (((w ⟨k, hk⟩).1, !(w ⟨k, hk⟩).2) : Dir d) = pos w k := by
    rw [dirVec_flip (w ⟨k, hk⟩), hstep]
    abel
  have hmem : s(pos w (k + 1), pos w (k + 1)
      + dirVec (((w ⟨k, hk⟩).1, !(w ⟨k, hk⟩).2) : Dir d)) ∈ E w (k + 1) := by
    have hsw : s(pos w (k + 1), pos w (k + 1)
        + dirVec (((w ⟨k, hk⟩).1, !(w ⟨k, hk⟩).2) : Dir d)) = edgeAt w k := by
      rw [hback]
      exact Sym2.eq_swap
    rw [hsw]
    exact Support.edgeAt_mem_E w (Nat.lt_succ_self k) hk
  -- so the reversed direction is missing from the set counted by `ν`
  unfold nu
  refine lt_of_le_of_lt (Finset.card_le_card
    (?_ : _ ⊆ Finset.univ.erase (((w ⟨k, hk⟩).1, !(w ⟨k, hk⟩).2) : Dir d))) ?_
  · intro x hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩
    rintro rfl
    exact (Finset.mem_filter.mp hx).2 hmem
  · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Support.card_dir]
    omega

/-- Hence `β ≤ μ_j` for `j ≥ 1` (`orrw.tex`). -/
theorem beta_le_mu (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) {n : ℕ} (w : Fin n → Dir d) {j : ℕ}
    (hj : 1 ≤ j) (hjn : j ≤ n) : β ≤ mu β w j := by
  have h1 : nu w j + 1 ≤ 2 * d := nu_lt hd w hj hjn
  have h2 : ((nu w j : ℕ) : ℝ) + 1 ≤ 2 * (d : ℝ) := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ ((nu w j : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ β * (2 * (d : ℝ) - ((nu w j : ℕ) : ℝ) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have h5 : β * (2 * (d : ℝ) - ((nu w j : ℕ) : ℝ)) + ((nu w j : ℕ) : ℝ)
      = β * (2 * (d : ℝ) - ((nu w j : ℕ) : ℝ) - 1) + ((nu w j : ℕ) : ℝ) + β := by ring
  unfold mu
  rw [h5]
  linarith

/-- The gradient of `g_R(· - z)` summed over the steps that cross a new edge is
at most the total variation of `g_R` over all edges of `ℤ^d`. -/
theorem sum_eta_grad_le {N : ℕ} (w : Fin N → Dir d) (R : ℕ) (z : Site d)
    {m h : ℕ} (hN : m + h ≤ N) :
    ∑ j ∈ Finset.Ico m (m + h),
        eta w (j + 1) * |gR R (pos w (j + 1) - z) - gR R (pos w j - z)|
      ≤ ∑' p : Site d × Fin d, |gR R (p.1 + dirVec (p.2, true)) - gR R p.1| := by
  classical
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simp only [Nat.add_zero, Finset.Ico_self, Finset.sum_empty]
    exact tsum_nonneg fun p => abs_nonneg _
  have hmN : m < N := by omega
  -- the parametrizing map: one pair `(x, i)` per undirected edge
  obtain ⟨iota, hiota⟩ : ∃ iota : ℕ → Site d × Fin d, ∀ (j : ℕ) (hj : j < N),
      iota j = if (w ⟨j, hj⟩).2 then (pos w j - z, (w ⟨j, hj⟩).1)
               else (pos w (j + 1) - z, (w ⟨j, hj⟩).1) := by
    refine ⟨fun j => if hj : j < N then
        (if (w ⟨j, hj⟩).2 then (pos w j - z, (w ⟨j, hj⟩).1)
          else (pos w (j + 1) - z, (w ⟨j, hj⟩).1))
      else (0, (w ⟨m, hmN⟩).1), fun j hj => ?_⟩
    exact dif_pos hj
  -- the value of the summand at `iota j`
  have hval : ∀ (j : ℕ) (hj : j < N),
      |gR R ((iota j).1 + dirVec ((iota j).2, true)) - gR R (iota j).1|
        = |gR R (pos w (j + 1) - z) - gR R (pos w j - z)| := by
    intro j hj
    have hs : pos w (j + 1) = pos w j + dirVec (w ⟨j, hj⟩) := pos_succ w j hj
    rw [hiota j hj]
    by_cases hb : (w ⟨j, hj⟩).2 = true
    · rw [if_pos hb]
      have he : (((w ⟨j, hj⟩).1, true) : Dir d) = w ⟨j, hj⟩ := by rw [← hb]
      simp only [he]
      have hx : pos w j - z + dirVec (w ⟨j, hj⟩) = pos w (j + 1) - z := by
        rw [hs]; abel
      rw [hx]
    · rw [if_neg hb]
      have hb' : (w ⟨j, hj⟩).2 = false := by simpa using hb
      have hfl : dirVec (((w ⟨j, hj⟩).1, true) : Dir d) = -dirVec (w ⟨j, hj⟩) := by
        have hflip := dirVec_flip (w ⟨j, hj⟩)
        simp only [hb', Bool.not_false] at hflip
        exact hflip
      simp only
      rw [hfl]
      have hx : pos w (j + 1) - z + -dirVec (w ⟨j, hj⟩) = pos w j - z := by
        rw [hs]; abel
      rw [hx, abs_sub_comm]
  -- the edge crossed at time `j` is the one named by `iota j`
  have hedge : ∀ (j : ℕ) (hj : j < N),
      s((iota j).1 + z, (iota j).1 + z + dirVec ((iota j).2, true)) = edgeAt w j := by
    intro j hj
    have hs : pos w (j + 1) = pos w j + dirVec (w ⟨j, hj⟩) := pos_succ w j hj
    rw [hiota j hj]
    by_cases hb : (w ⟨j, hj⟩).2 = true
    · rw [if_pos hb]
      have he : (((w ⟨j, hj⟩).1, true) : Dir d) = w ⟨j, hj⟩ := by rw [← hb]
      simp only [he]
      have hx : pos w j - z + z = pos w j := by abel
      rw [hx, ← hs]
      rfl
    · rw [if_neg hb]
      have hb' : (w ⟨j, hj⟩).2 = false := by simpa using hb
      have hfl : dirVec (((w ⟨j, hj⟩).1, true) : Dir d) = -dirVec (w ⟨j, hj⟩) := by
        have hflip := dirVec_flip (w ⟨j, hj⟩)
        simp only [hb', Bool.not_false] at hflip
        exact hflip
      simp only
      rw [hfl]
      have hx : pos w (j + 1) - z + z = pos w (j + 1) := by abel
      rw [hx]
      have hy : pos w (j + 1) + -dirVec (w ⟨j, hj⟩) = pos w j := by
        rw [hs]; abel
      rw [hy]
      exact Sym2.eq_swap
  -- the steps that cross a new edge
  set T : Finset ℕ := (Finset.Ico m (m + h)).filter (fun j => eta w (j + 1) = 1) with hT
  have hTsub : T ⊆ Finset.Ico m (m + h) := Finset.filter_subset _ _
  have hTlt : ∀ j ∈ T, j < N := by
    intro j hjT
    have := (Finset.mem_Ico.mp (hTsub hjT)).2
    omega
  have heta01 : ∀ k : ℕ, eta w k = 0 ∨ eta w k = 1 := by
    intro k
    unfold eta
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  -- distinct new edges: `iota` is injective on `T`
  have hne : ∀ x ∈ T, ∀ y ∈ T, x < y → iota x ≠ iota y := by
    intro x hxT y hyT hlt heq
    have hxN : x < N := hTlt x hxT
    have hyN : y < N := hTlt y hyT
    have hedgeeq : edgeAt w x = edgeAt w y := by
      rw [← hedge x hxN, ← hedge y hyN, heq]
    have hmemE : edgeAt w y ∈ E w y := by
      rw [← hedgeeq]
      exact Support.edgeAt_mem_E w hlt hxN
    have hEeq : E w (y + 1) = E w y := by
      rw [Support.E_succ_eq w hyN, Finset.insert_eq_self.mpr hmemE]
    have hetay : eta w (y + 1) = 1 := by
      rw [hT] at hyT
      exact (Finset.mem_filter.mp hyT).2
    have hzeroy : eta w (y + 1) = 0 := by
      unfold eta
      rw [Nat.add_sub_cancel, hEeq]
      simp
    rw [hzeroy] at hetay
    norm_num at hetay
  have hinj : Set.InjOn iota ↑T := by
    intro x hx y hy hxy
    have hxT : x ∈ T := hx
    have hyT : y ∈ T := hy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact absurd hxy (hne x hxT y hyT hlt)
    · exact heq
    · exact absurd hxy.symm (hne y hyT x hxT hgt)
  -- only the steps in `T` contribute
  have hsum1 : ∑ j ∈ Finset.Ico m (m + h),
        eta w (j + 1) * |gR R (pos w (j + 1) - z) - gR R (pos w j - z)|
      = ∑ j ∈ T, |gR R (pos w (j + 1) - z) - gR R (pos w j - z)| := by
    rw [← Finset.sum_subset hTsub ?_]
    · refine Finset.sum_congr rfl fun j hjT => ?_
      have : eta w (j + 1) = 1 := by
        rw [hT] at hjT
        exact (Finset.mem_filter.mp hjT).2
      rw [this, one_mul]
    · intro x hx hxT
      rcases heta01 (x + 1) with h0 | h1
      · rw [h0, zero_mul]
      · exact absurd (by rw [hT]; exact Finset.mem_filter.mpr ⟨hx, h1⟩) hxT
  rw [hsum1]
  have hsum2 : ∑ j ∈ T, |gR R (pos w (j + 1) - z) - gR R (pos w j - z)|
      = ∑ p ∈ T.image iota, |gR R (p.1 + dirVec (p.2, true)) - gR R p.1| := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun j hjT => (hval j (hTlt j hjT)).symm
  rw [hsum2]
  exact Summable.sum_le_tsum _ (fun p _ => abs_nonneg _) (summable_gR_gradient R)

end ORRW
