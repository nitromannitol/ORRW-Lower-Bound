import Mathlib

/-!
# Theorem 1.3 (`thm:occupation-intro`): comparator challenge

Mathlib-only comparator challenge for Theorem 1.3 (`thm:occupation-intro`) of Ahmed Bou-Rabee and Yuval
Peres, *Once-reinforced random walk on `ℤ^d` has range exponent at least
`d/(d+1)`*.  The certified statement is `ORRW.Frozen.occupation_measure`, restated in
`ORRW/MainTheorems.lean` as `ORRW.occupation_measure`.  Content: for `d ≥ 2` there is a constant `C` such that
`∑_{j<n} P_β(X_j = z) ≤ C β n^{1/(d+1)}` for every `β ≥ 1`, every `n ≥ 1` and
every site `z`.  The left side is the expected local time `E_β L_n(z)`, read in
the law of the first `N` steps for any horizon `N ≥ n`.

Only Mathlib is imported.  The vocabulary between `VOCABULARY-BEGIN` and
`VOCABULARY-END` rebuilds, from Mathlib primitives, every definition needed to
read the theorem: the lattice `ℤ^d`, its `2d` directions and the position of a
direction word; the traversed edges, the range and the step rule of
once-reinforced random walk; its law on words of length `n`, with expectation
and probability; and its law on infinite direction words, built by the
Ionescu-Tulcea theorem.  It is a statement-level copy of the repository
definitions (see `Audit/README.md` for the provenance table) and is
byte-identical in all four challenges.  The sole intentional `sorry` is the
proof of the final theorem.

## Cited results

None.  The theorem takes no cited result as a hypothesis, and neither does
this challenge.

## Presentation deltas

None at the level of the displayed statement: the theorem below is the
statement of `ORRW.occupation_measure` with every repository name replaced by its
vocabulary copy.
-/

-- VOCABULARY-BEGIN
namespace ORRWAudit

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal

/-! ## 1. The lattice and direction words (`orrw.tex:100-110`) -/

/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- A direction: a coordinate together with a sign.  There are `2d` of them. -/
abbrev Dir (d : ℕ) := Fin d × Bool

/-- The unit vector `± e_i` named by a direction. -/
def dirVec {d : ℕ} (a : Dir d) : Site d :=
  fun j => if j = a.1 then (if a.2 then 1 else -1) else 0

/-- Position after `k` steps of the direction word `w`; the walk starts at the
origin, and `pos` is constant once `k` reaches the length of the word. -/
def pos {d n : ℕ} (w : Fin n → Dir d) (k : ℕ) : Site d :=
  ∑ i : Fin n, if (i : ℕ) < k then dirVec (w i) else 0

/-- The undirected edge crossed by step `i + 1`. -/
def edgeAt {d n : ℕ} (w : Fin n → Dir d) (i : ℕ) : Sym2 (Site d) :=
  s(pos w i, pos w (i + 1))

/-! ## 2. Once-reinforced random walk (`orrw.tex:100-110`) -/

/-- `E w k`: the set of undirected edges crossed in the first `k` steps, the
paper's `E_k`; `E w 0 = ∅`. -/
def E {d n : ℕ} (w : Fin n → Dir d) (k : ℕ) : Finset (Sym2 (Site d)) :=
  (range (min k n)).image (edgeAt w)

/-- `R w k`: the range `R_k = {X_0, …, X_k}`. -/
def R {d n : ℕ} (w : Fin n → Dir d) (k : ℕ) : Finset (Site d) :=
  (range (k + 1)).image (pos w)

/-- The weight of the edge from the current site along direction `a`, at time
`k`: `β` if that edge has already been crossed, and `1` otherwise. -/
def stepWeight {d n : ℕ} (β : ℝ) (w : Fin n → Dir d) (k : ℕ) (a : Dir d) : ℝ :=
  if s(pos w k, pos w k + dirVec a) ∈ E w k then β else 1

/-- The total weight at the current site: the denominator of the step rule. -/
def totalWeight {d n : ℕ} (β : ℝ) (w : Fin n → Dir d) (k : ℕ) : ℝ :=
  ∑ a : Dir d, stepWeight β w k a

/-- The conditional probability of the step actually taken at time `k`. -/
noncomputable def stepProb {d n : ℕ} (β : ℝ) (w : Fin n → Dir d) (k : Fin n) : ℝ :=
  stepWeight β w k (w k) / totalWeight β w k

/-- The law of the first `n` steps of once-reinforced random walk with
parameter `β`, as a mass function on direction words. -/
noncomputable def prob {d n : ℕ} (β : ℝ) (w : Fin n → Dir d) : ℝ :=
  ∏ k : Fin n, stepProb β w k

/-- `𝔼_β` of a function of the first `n` steps. -/
noncomputable def expect {d : ℕ} (n : ℕ) (β : ℝ) (f : (Fin n → Dir d) → ℝ) : ℝ :=
  ∑ w : Fin n → Dir d, prob β w * f w

open Classical in
/-- `ℙ_β` of an event depending on the first `n` steps. -/
noncomputable def prb {d : ℕ} (n : ℕ) (β : ℝ) (P : (Fin n → Dir d) → Prop) : ℝ :=
  ∑ w : Fin n → Dir d, prob β w * (if P w then 1 else 0)

/-! ## 3. The law of the walk on infinite direction words -/

/-- The first `n + 1` letters of a trajectory prefix indexed by `Iic n`. -/
def ofPrefix {d : ℕ} (n : ℕ) (x : Π _i : Iic n, Dir d) : Fin (n + 1) → Dir d :=
  fun i => x ⟨i, mem_Iic.mpr (Nat.lt_succ_iff.mp i.isLt)⟩

/-- The first `n` letters of an infinite word. -/
def ofPath {d : ℕ} (n : ℕ) (ω : Π _k : ℕ, Dir d) : Fin n → Dir d := fun i => ω i

/-- The one-step law: given the letters `0, …, n`, the law of letter `n + 1`. -/
noncomputable def stepPMF {d : ℕ} (β : ℝ) (n : ℕ) (x : Π _i : Iic n, Dir d) (a : Dir d) :
    ℝ≥0∞ :=
  ENNReal.ofReal
    (stepWeight β (ofPrefix n x) (n + 1) a / totalWeight β (ofPrefix n x) (n + 1))

/-- The law of the first letter, uniform on the `2d` directions. -/
noncomputable def initPMF {d : ℕ} (β : ℝ) (a : Dir d) : ℝ≥0∞ :=
  ENNReal.ofReal
    (stepWeight β (d := d) (n := 0) (fun i => i.elim0) 0 a
      / totalWeight β (d := d) (n := 0) (fun i => i.elim0) 0)

/-- The one-step kernel of the walk, as a measure on the next letter. -/
noncomputable def stepMeasure {d : ℕ} (β : ℝ) (n : ℕ) (x : Π _i : Iic n, Dir d) :
    Measure (Dir d) :=
  ∑ a : Dir d, stepPMF β n x a • Measure.dirac a

/-- The law of the first letter, as a measure. -/
noncomputable def initMeasure {d : ℕ} (β : ℝ) : Measure (Dir d) :=
  ∑ a : Dir d, initPMF β a • Measure.dirac a

/-- The one-step kernel. -/
noncomputable def kappa {d : ℕ} (β : ℝ) (n : ℕ) :
    Kernel (Π _i : Iic n, Dir d) (Dir d) where
  toFun := stepMeasure β n
  measurable' := by
    apply Measurable.of_discrete

/-- The total weight is positive when `0 < d` and `1 ≤ β`. -/
theorem totalWeight_pos {d n : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β)
    (w : Fin n → Dir d) (k : ℕ) : 0 < totalWeight β w k :=
  Finset.sum_pos (fun a _ => by unfold stepWeight; split <;> linarith)
    ⟨(⟨0, hd⟩, true), Finset.mem_univ _⟩

/-- The one-step kernels are Markov kernels. -/
theorem isMarkovKernel_kappa {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) (n : ℕ) :
    IsMarkovKernel (kappa (d := d) β n) := by
  refine ⟨fun x => ⟨?_⟩⟩
  show stepMeasure β n x Set.univ = 1
  rw [stepMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  have htpos := totalWeight_pos hd hβ (ofPrefix n x) (n + 1)
  unfold stepPMF
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => div_nonneg
      (by unfold stepWeight; split <;> linarith) (le_of_lt htpos)),
    ← Finset.sum_div]
  exact (congrArg ENNReal.ofReal (div_self (ne_of_gt htpos))).trans ENNReal.ofReal_one

instance instIsMarkovKernel_kappa {d : ℕ} [hd : Fact (0 < d)] {β : ℝ} [hβ : Fact (1 ≤ β)]
    (n : ℕ) : IsMarkovKernel (kappa (d := d) β n) :=
  isMarkovKernel_kappa hd.out hβ.out n

/-- The law of the first letter, as a measure on `Π i : Iic 0, Dir d`. -/
noncomputable def initTraj {d : ℕ} (β : ℝ) : Measure (Π _i : Iic (0 : ℕ), Dir d) :=
  (initMeasure (d := d) β).map (fun a _ => a)

/-- The law of once-reinforced random walk on infinite direction words, built
from the one-step kernels by the Ionescu-Tulcea theorem (`Kernel.traj`). -/
noncomputable def pathMeasure {d : ℕ} [Fact (0 < d)] (β : ℝ) [Fact (1 ≤ β)] :
    Measure (Π _k : ℕ, Dir d) :=
  (Kernel.traj (X := fun _ => Dir d) (kappa β) 0) ∘ₘ (initTraj β)

end ORRWAudit
-- VOCABULARY-END

namespace ORRWAudit

open MeasureTheory Filter

/-- Theorem 1.3 (`thm:occupation-intro`), the occupation measure bound. -/
theorem occupation_measure (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, 1 ≤ n → ∀ N : ℕ, n ≤ N → ∀ z : Site d,
      ∑ j ∈ Finset.range n, prb (d := d) N β (fun w => pos w j = z)
        ≤ C * β * (n : ℝ) ^ (1 / ((d : ℝ) + 1)) := by
  sorry

end ORRWAudit
