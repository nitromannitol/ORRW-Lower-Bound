/-
Conditioning on a prefix, in the finite-word model of ruling R-001.

`ORRW.prob` is a mass function on `Fin n → Dir d`.  Two identities let an
expectation at horizon `n + 1` be computed from horizon `n`: summing the last
letter out of a quantity that does not see it (`expect_init`), and expanding a
general expectation over the last letter with the step rule (`expect_snoc`).
Section 8 of `orrw.tex` uses them to evaluate the compensator `eq:compensator`
at one time, which is a statement about `F_j`-conditional expectations.
-/
import Mathlib
import ORRW.Basic
import ORRW.Support.Guards

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ORRW

open Finset

variable {d : ℕ}

/-- Reindexing a sum over words of length `n + 1` as a sum over a last letter
together with a word of length `n`, with the word sum on the outside. -/
private theorem sum_snoc_reindex {n : ℕ} (F : (Fin (n + 1) → Dir d) → ℝ) :
    ∑ w : Fin (n + 1) → Dir d, F w
      = ∑ v : Fin n → Dir d, ∑ a : Dir d, F (Fin.snoc v a) := by
  have key : ∑ w : Fin (n + 1) → Dir d, F w
      = ∑ p : Dir d × (Fin n → Dir d), F (Fin.snoc p.2 p.1) :=
    (Fintype.sum_equiv (Fin.snocEquiv (fun _ => Dir d))
      (fun p => F (Fin.snoc p.2 p.1)) (fun w => F w) (fun _ => rfl)).symm
  rw [key, Fintype.sum_prod_type, Finset.sum_comm]

/-- An expectation of a quantity that does not read the last letter drops to the
shorter horizon. -/
theorem expect_init (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) {n : ℕ} (G : (Fin n → Dir d) → ℝ) :
    ∑ w : Fin (n + 1) → Dir d, prob β w * G (Fin.init w)
      = ∑ v : Fin n → Dir d, prob β v * G v := by
  rw [sum_snoc_reindex (fun w => prob β w * G (Fin.init w))]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Fin.init_snoc]
  rw [← Finset.sum_mul, sum_prob_snoc hd hβ v]

/-- An expectation at horizon `n + 1` expanded over the last letter, with the
step rule as the conditional law. -/
theorem expect_snoc {β : ℝ} {n : ℕ} (G : (Fin (n + 1) → Dir d) → ℝ) :
    ∑ w : Fin (n + 1) → Dir d, prob β w * G w
      = ∑ v : Fin n → Dir d, ∑ a : Dir d,
          prob β v * (stepWeight β v n a / totalWeight β v n) * G (Fin.snoc v a) := by
  rw [sum_snoc_reindex (fun w => prob β w * G w)]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun a _ => ?_
  rw [prob_succ β (Fin.snoc v a), Fin.init_snoc, Fin.snoc_last]

end ORRW
