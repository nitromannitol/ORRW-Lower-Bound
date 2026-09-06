/-
The one geometric input to Proposition 6.1 of Bou-Rabee--Peres,
`orrw.tex` (`eq:range-box`):

  "The only geometric input is that the range at time `n` lies in the box of
   radius `Λ_n`, that is, `|R_n| ≤ (2Λ_n+1)^d`."

Nothing here is frozen.
-/
import ORRW.Basic
import ORRW.Support.Guards

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW.Support

open Finset ORRW

variable {d n : ℕ}

/-- A site whose sup norm is at most `r` has every coordinate in `[-r, r]`. -/
lemma mem_box_of_norm_le {r : ℕ} {x : Site d} (hx : ‖x‖ ≤ (r : ℝ)) :
    x ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ)) := by
  refine Fintype.mem_piFinset.mpr fun i => ?_
  have hcoord : ‖x i‖ ≤ (r : ℝ) := le_trans (norm_le_pi_norm x i) hx
  rw [Int.norm_eq_abs] at hcoord
  have habs : |x i| ≤ (r : ℤ) := by exact_mod_cast hcoord
  exact Finset.mem_Icc.mpr (abs_le.mp habs)

/-- The box of radius `r` has `(2r+1)^d` sites. -/
lemma card_box (r : ℕ) :
    (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ))).card
      = (2 * r + 1) ^ d := by
  rw [Fintype.card_piFinset]
  have hIcc : ∀ _i : Fin d, (Finset.Icc (-(r : ℤ)) (r : ℤ)).card = 2 * r + 1 := by
    intro _i
    rw [Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl fun i _ => hIcc i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- `eq:range-box`: the range at time `k` lies in the box of radius `r`, so it
has at most `(2r+1)^d` sites. -/
theorem card_range_le_box (w : Fin n → Dir d) (k r : ℕ)
    (hr : ∀ j ≤ k, ‖pos w j‖ ≤ (r : ℝ)) :
    (R w k).card ≤ (2 * r + 1) ^ d := by
  classical
  have hsub : R w k ⊆ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ)) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact mem_box_of_norm_le (hr j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  calc (R w k).card
      ≤ (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ))).card :=
        Finset.card_le_card hsub
    _ = (2 * r + 1) ^ d := card_box r

end ORRW.Support
