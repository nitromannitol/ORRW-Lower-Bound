/-
The infinite-path measure, and the almost-sure statements that need it.

Ruling R-001 models the law of the first `n` steps as a mass function on the
finite set of direction words `Fin n → Dir d`.  That is enough for every bound
the paper states at a fixed time, but not for its two almost-sure corollaries,
which quantify over all times at once under a single measure.  This file builds
that measure by the Ionescu-Tulcea theorem from the one-step kernels, and
identifies its finite-dimensional marginals with `ORRW.prob`.

Nothing here is frozen; `ORRW/Frozen/AlmostSure.lean` states what the paper
claims.
-/
import Mathlib
import ORRW.Basic
import ORRW.Support.Guards

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal

namespace ORRW

variable {d : ℕ}

/-- The first `n + 1` letters of a trajectory prefix indexed by `Iic n`. -/
def ofPrefix (n : ℕ) (x : Π _i : Iic n, Dir d) : Fin (n + 1) → Dir d :=
  fun i => x ⟨i, mem_Iic.mpr (Nat.lt_succ_iff.mp i.isLt)⟩

/-- The first `n` letters of an infinite word. -/
def ofPath (n : ℕ) (ω : Π _k : ℕ, Dir d) : Fin n → Dir d := fun i => ω i

/-- The first `n + 1` letters of an infinite word, indexed by `Iic n`.  This is
Mathlib's `frestrictLe n`, written out so that its implicit type family does not
have to be supplied at every use. -/
def restr (n : ℕ) (ω : Π _k : ℕ, Dir d) : Π _i : Iic n, Dir d := fun i => ω i

/-- The path measure restricted to the first `n` steps agrees with the finite-time model, so almost-sure statements inherit the fixed-time bounds. -/
theorem restr_eq_frestrictLe (n : ℕ) :
    restr (d := d) n = frestrictLe n := rfl

/-- The one-step law: given the letters `0, …, n`, the law of letter `n + 1`.
The weights are those of `stepWeight` at time `n + 1`, which reads only the
letters already fixed. -/
noncomputable def stepPMF (β : ℝ) (n : ℕ) (x : Π _i : Iic n, Dir d) (a : Dir d) : ℝ≥0∞ :=
  ENNReal.ofReal
    (stepWeight β (ofPrefix n x) (n + 1) a / totalWeight β (ofPrefix n x) (n + 1))

/-- The law of the first letter: all `2d` edges at the origin are untraversed,
so it is uniform. -/
noncomputable def initPMF (β : ℝ) (a : Dir d) : ℝ≥0∞ :=
  ENNReal.ofReal
    (stepWeight β (d := d) (n := 0) (fun i => i.elim0) 0 a
      / totalWeight β (d := d) (n := 0) (fun i => i.elim0) 0)

/-- The one-step kernel of the walk, as a measure on the next letter. -/
noncomputable def stepMeasure (β : ℝ) (n : ℕ) (x : Π _i : Iic n, Dir d) : Measure (Dir d) :=
  ∑ a : Dir d, stepPMF β n x a • Measure.dirac a

/-- The law of the first letter, as a measure. -/
noncomputable def initMeasure (β : ℝ) : Measure (Dir d) :=
  ∑ a : Dir d, initPMF β a • Measure.dirac a

/-- The one-step kernel.  The domain is a finite discrete space, so there is
nothing to check for measurability. -/
noncomputable def kappa (β : ℝ) (n : ℕ) :
    Kernel (Π _i : Iic n, Dir d) (Dir d) where
  toFun := stepMeasure β n
  measurable' := by
    apply Measurable.of_discrete

/-- The one-step weights normalise: this is what makes `kappa` a Markov kernel,
and it is where `totalWeight_pos` earns its place -- without it the quotient
would be `0 / 0 = 0` and the kernel would have mass `0`. -/
theorem sum_stepPMF (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) (n : ℕ)
    (x : Π _i : Iic n, Dir d) : ∑ a : Dir d, stepPMF β n x a = 1 := by
  have htpos := ORRW.totalWeight_pos hd hβ (ofPrefix n x) (n+1)
  have hw : ∀ a ∈ (Finset.univ : Finset (Dir d)),
      0 ≤ ORRW.stepWeight β (ofPrefix n x) (n+1) a := by
    intro a _
    unfold ORRW.stepWeight
    split <;> linarith
  unfold stepPMF
  rw [← ENNReal.ofReal_sum_of_nonneg
      (fun a _ => div_nonneg (hw a (Finset.mem_univ a)) (le_of_lt htpos))]
  rw [← Finset.sum_div]
  show ENNReal.ofReal
      (ORRW.totalWeight β (ofPrefix n x) (n+1) /
        ORRW.totalWeight β (ofPrefix n x) (n+1)) = 1
  rw [div_self (ne_of_gt htpos), ENNReal.ofReal_one]

/-- The one-step kernels assemble into a Markov kernel, the hypothesis needed to invoke the Ionescu-Tulcea theorem when constructing the infinite-path measure. -/
theorem isMarkovKernel_kappa (hd : 0 < d) {β : ℝ} (hβ : 1 ≤ β) (n : ℕ) :
    IsMarkovKernel (kappa (d := d) β n) := by
  refine ⟨fun x => ⟨?_⟩⟩
  show stepMeasure β n x Set.univ = 1
  rw [stepMeasure]
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact sum_stepPMF hd hβ n x

/-- `traj` needs the Markov property as an instance, and that property needs
`0 < d` and `1 ≤ β`.  Carrying them as `Fact`s is the idiomatic way to let
/-- Provides the Markov kernel structure needed to invoke Ionescu-Tulcea when constructing the infinite-path measure from the one-step kernels. -/
instance resolution see a hypothesis. -/
instance instIsMarkovKernel_kappa [hd : Fact (0 < d)] {β : ℝ} [hβ : Fact (1 ≤ β)] (n : ℕ) :
    IsMarkovKernel (kappa (d := d) β n) :=
  isMarkovKernel_kappa hd.out hβ.out n

/-- The law of the first letter, as a measure on `Π i : Iic 0, Dir d`. -/
noncomputable def initTraj (β : ℝ) : Measure (Π _i : Iic (0 : ℕ), Dir d) :=
  (initMeasure (d := d) β).map (fun a _ => a)

/-- **The law of the walk on infinite direction words.**  Built from the
one-step kernels by the Ionescu-Tulcea theorem, so that every time is measured
by one and the same measure.  This is what ruling R-001 does without, and it is
what the paper's two almost-sure corollaries need. -/
noncomputable def pathMeasure [Fact (0 < d)] (β : ℝ) [Fact (1 ≤ β)] :
    Measure (Π _k : ℕ, Dir d) :=
  (Kernel.traj (X := fun _ => Dir d) (kappa β) 0) ∘ₘ (initTraj β)

set_option maxHeartbeats 1000000 in
/-- Step 1 of the bridge: the infinite-path measure of a cylinder is the
`initTraj`-average of `partialTraj`.  This is the only place Ionescu-Tulcea is
used; what remains is a finite computation. -/
theorem pathMeasure_restr_eq_bind [Fact (0 < d)] {β : ℝ} [Fact (1 ≤ β)] (n : ℕ)
    (x : Π _i : Iic n, Dir d) :
    pathMeasure (d := d) β {ω | restr n ω = x}
      = ∫⁻ a, (Kernel.partialTraj (X := fun _ => Dir d) (kappa β) 0 n a) {x}
          ∂(initTraj β) := by
  have hmeas : Measurable (restr (d := d) n) := by
    rw [restr_eq_frestrictLe]; exact measurable_frestrictLe n
  have hset : {ω : (Π _k : ℕ, Dir d) | restr n ω = x} = (restr n) ⁻¹' {x} := rfl
  rw [pathMeasure, hset]
  rw [Measure.bind_apply (hmeas (measurableSet_singleton x))
    (Kernel.traj (kappa β) 0).aemeasurable]
  refine lintegral_congr fun a => ?_
  have hmap := Kernel.traj_map_frestrictLe_apply (X := fun _ => Dir d)
    (κ := kappa β) 0 n a
  have hset2 : restr (d := d) n ⁻¹' ({x} : Set (Π _i : Iic n, Dir d))
      = frestrictLe n ⁻¹' ({x} : Set (Π _i : Iic n, Dir d)) := by
    rw [restr_eq_frestrictLe]
  rw [hset2, ← Measure.map_apply (measurable_frestrictLe (X := fun _ : ℕ => Dir d) n)
    (measurableSet_singleton x), hmap]


set_option maxHeartbeats 1000000 in
/-- One step of `partialTraj`, evaluated at a single word.  `IicProdIoc` is a
measurable equivalence when `a ≤ b`, so the preimage of a singleton is a
singleton, and the product measure factors. -/
theorem partialTraj_step_singleton [Fact (0 < d)] {β : ℝ} [Fact (1 ≤ β)] (n : ℕ)
    (y : Π _i : Iic n, Dir d) (x : Π _i : Iic (n+1), Dir d) :
    (Kernel.partialTraj (X := fun _ => Dir d) (kappa β) n (n+1) y) {x}
      = (Measure.dirac y) {(MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => Dir d)
            (Nat.le_succ n)).symm x |>.1}
        * ((kappa β n y).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Dir d) n))
            {(MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => Dir d)
              (Nat.le_succ n)).symm x |>.2} := by
  rw [Kernel.partialTraj_succ_self]
  rw [Kernel.map_apply _ (measurable_IicProdIoc (X := fun _ : ℕ => Dir d)) y]
  rw [Measure.map_apply (measurable_IicProdIoc (X := fun _ : ℕ => Dir d))
    (measurableSet_singleton x)]
  rw [Kernel.prod_apply, Kernel.id_apply]
  have hpre : (IicProdIoc (X := fun _ : ℕ => Dir d) n (n+1)) ⁻¹' {x}
      = ({((MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => Dir d) (Nat.le_succ n)).symm x).1}
          : Set (Π _i : Iic n, Dir d))
        ×ˢ ({((MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => Dir d) (Nat.le_succ n)).symm x).2}
          : Set (Π _i : Ioc n (n+1), Dir d)) := by
    rw [Set.singleton_prod_singleton, ← MeasurableEquiv.coe_IicProdIoc (Nat.le_succ n)]
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [Prod.mk.eta]
    exact (MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => Dir d)
      (Nat.le_succ n)).toEquiv.apply_eq_iff_eq_symm_apply
  rw [hpre, Measure.prod_prod,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Dir d) n).measurable y]


/-- The one-step measure at a single letter is its mass function. -/
theorem stepMeasure_singleton (β : ℝ) (n : ℕ) (y : Π _i : Iic n, Dir d) (b : Dir d) :
    stepMeasure β n y {b} = stepPMF β n y b := by
  rw [stepMeasure, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hcb
    simp [hcb]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- The kernel at a single letter. -/
theorem kappa_singleton (β : ℝ) (n : ℕ) (y : Π _i : Iic n, Dir d) (b : Dir d) :
    (kappa (d := d) β n y) {b} = stepPMF β n y b :=
  stepMeasure_singleton β n y b

/-- The restriction of an `Iic (n+1)`-word to `Iic n`. -/
def trunc (n : ℕ) (x : Π _i : Iic (n+1), Dir d) : Π _i : Iic n, Dir d :=
  fun i => x ⟨i.1, mem_Iic.2 ((mem_Iic.1 i.2).trans (Nat.le_succ n))⟩

/-- The last letter of an `Iic (n+1)`-word. -/
def lastOf (n : ℕ) (x : Π _i : Iic (n+1), Dir d) : Dir d :=
  x ⟨n + 1, mem_Iic.2 le_rfl⟩

set_option maxHeartbeats 1000000 in
/-- One step of `partialTraj`, in closed form: it advances a word by one letter,
weighting by the one-step mass function, and kills every word that does not
extend the given prefix. -/
theorem partialTraj_step_eval [Fact (0 < d)] {β : ℝ} [Fact (1 ≤ β)] (n : ℕ)
    (y : Π _i : Iic n, Dir d) (x : Π _i : Iic (n+1), Dir d) :
    (Kernel.partialTraj (X := fun _ => Dir d) (kappa β) n (n+1) y) {x}
      = if y = trunc n x then stepPMF β n y (lastOf n x) else 0 := by
  rw [partialTraj_step_singleton]
  have h1 : ((MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => Dir d)
      (Nat.le_succ n)).symm x).1 = trunc n x := rfl
  have h2 : (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Dir d) n).symm
      (((MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => Dir d)
        (Nat.le_succ n)).symm x).2) = lastOf n x := rfl
  rw [h1, Measure.map_apply (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Dir d) n).measurable
    (measurableSet_singleton _)]
  have h3 : (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Dir d) n) ⁻¹'
      {((MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => Dir d) (Nat.le_succ n)).symm x).2}
      = {lastOf n x} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← h2]
    exact (Equiv.eq_symm_apply _).symm
  rw [h3, kappa_singleton, Measure.dirac_apply]
  by_cases hy : y = trunc n x
  · simp [hy]
  · simp [hy]

/-- The initial measure at a single letter. -/
theorem initMeasure_singleton (β : ℝ) (b : Dir d) :
    initMeasure (d := d) β {b} = initPMF β b := by
  rw [initMeasure, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hcb; simp [hcb]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- The law of the first letter, at a single one-letter word. -/
theorem initTraj_singleton (β : ℝ) (x : Π _i : Iic (0 : ℕ), Dir d) :
    initTraj (d := d) β {x} = initPMF β (x ⟨0, mem_Iic.2 le_rfl⟩) := by
  rw [initTraj, Measure.map_apply (by fun_prop) (measurableSet_singleton x)]
  have : ((fun (a : Dir d) (_ : Iic (0 : ℕ)) => a) ⁻¹' {x})
      = {x ⟨0, mem_Iic.2 le_rfl⟩} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h; exact (congrFun h ⟨0, mem_Iic.2 le_rfl⟩).symm ▸ rfl
    · rintro rfl
      funext i
      obtain ⟨i, hi⟩ := i
      have : i = 0 := Nat.le_zero.1 (mem_Iic.1 hi)
      subst this; rfl
  rw [this, initMeasure_singleton]

set_option maxHeartbeats 2000000 in
/-- **The induction.**  The `initTraj`-average of `partialTraj` at a single word
is that word's `prob`.  The step is `partialTraj_step_eval`, which turns the
inner integral into a point evaluation, and `prob_succ`, which is the matching
recursion on the finite-word side. -/
theorem bind_partialTraj_eval [Fact (0 < d)] {β : ℝ} [Fact (1 ≤ β)] :
    ∀ (n : ℕ) (x : Π _i : Iic n, Dir d),
      ∫⁻ a, (Kernel.partialTraj (X := fun _ => Dir d) (kappa β) 0 n a) {x} ∂(initTraj β)
        = ENNReal.ofReal (prob β (ofPrefix n x)) := by
  intro n
  induction n with
  | zero =>
    intro x
    simp only [Kernel.partialTraj_self, Kernel.id_apply, Measure.dirac_apply]
    rw [lintegral_indicator (measurableSet_singleton x)]
    simp only [lintegral_const, Measure.restrict_apply_univ, Pi.one_apply, one_mul]
    rw [initTraj_singleton, initPMF, prob_succ]
    have hinit : Fin.init (ofPrefix 0 x) = (fun i : Fin 0 => i.elim0) := by
      funext i; exact i.elim0
    rw [hinit]
    simp only [prob, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    rfl
  | succ n ih =>
    intro x
    have hcomp : ∀ a : Π _i : Iic (0:ℕ), Dir d,
        (Kernel.partialTraj (X := fun _ => Dir d) (kappa β) 0 (n+1) a) {x}
          = stepPMF β n (trunc n x) (lastOf n x)
            * (Kernel.partialTraj (X := fun _ => Dir d) (kappa β) 0 n a) {trunc n x} := by
      intro a
      rw [← Kernel.partialTraj_comp_partialTraj (zero_le n) (Nat.le_succ n),
        Kernel.comp_apply, Measure.bind_apply (measurableSet_singleton x)
          (Kernel.partialTraj (X := fun _ => Dir d) (kappa β) n (n+1)).aemeasurable]
      have hint : ∀ y : Π _i : Iic n, Dir d,
          (Kernel.partialTraj (X := fun _ => Dir d) (kappa β) n (n+1) y) {x}
            = Set.indicator {trunc n x}
                (fun _ => stepPMF β n (trunc n x) (lastOf n x)) y := by
        intro y
        rw [partialTraj_step_eval]
        by_cases hy : y = trunc n x
        · simp [hy]
        · simp [hy]
      simp only [hint]
      rw [lintegral_indicator (measurableSet_singleton _), lintegral_const,
        Measure.restrict_apply_univ]
    simp only [hcomp]
    rw [lintegral_const_mul _ (by fun_prop), ih (trunc n x)]
    conv_rhs => rw [prob_succ]
    have hinit : Fin.init (ofPrefix (n+1) x) = ofPrefix n (trunc n x) := by
      funext i; rfl
    have hlast : (ofPrefix (n+1) x) (Fin.last (n+1)) = lastOf n x := rfl
    rw [hinit, hlast, stepPMF]
    have hnn : (0:ℝ) ≤ stepWeight β (ofPrefix n (trunc n x)) (n+1) (lastOf n x)
        / totalWeight β (ofPrefix n (trunc n x)) (n+1) := by
      refine div_nonneg ?_ (totalWeight_pos (Fact.out : 0 < d) (Fact.out : (1:ℝ) ≤ β) _ _).le
      unfold stepWeight
      split
      · exact le_trans zero_le_one (Fact.out : (1:ℝ) ≤ β)
      · norm_num
    rw [← ENNReal.ofReal_mul hnn, mul_comm]


/-- The first `n + 1` letters of `ω`, read through `Iic n`, are its first
`n + 1` letters read through `Fin (n + 1)`. -/
theorem ofPath_restr (n : ℕ) (ω : Π _k : ℕ, Dir d) :
    ofPath (n + 1) ω = ofPrefix n (restr n ω) := by
  funext i
  rfl

end ORRW
