/-
Once-reinforced random walk on `ℤ^d`: the model.

Encodes  Bou-Rabee--Peres, *Once-reinforced random walk on `ℤ^d` has range
exponent at least `d/(d+1)`*, Section 1.1 (`ssec:main-results`),
`orrw.tex`:

  "Fix an integer `d ≥ 2` and a reinforcement parameter `β ≥ 1`.  Let `(X_n)`
   be once-reinforced random walk started at the origin of `ℤ^d`, and let
   `E_n := {{X_{i-1}, X_i} : 1 ≤ i ≤ n}` be the set of undirected edges it has
   crossed in its first `n` steps, so that `E_0 = ∅`.  Given `X_0, …, X_n`, the
   walk steps from `X_n` to a neighbor `y` with probability proportional to `β`
   if `{X_n, y} ∈ E_n` and proportional to `1` otherwise. ...
   The range at time `n` is `R_n := {X_0, …, X_n}`."

Modelling decision (ruling R-001).  The law of the first `n` steps is a
probability mass function on the *finite* set of direction words
`Fin n → Dir d`, not a measure on infinite paths.  Every quantity the paper's
two main theorems mention (`|R_n|`, `|E_n|`, `S_n`, `σ_k ∧ n`) is a function of
the first `n` steps, so no infinite-horizon measure is needed and no
measurability side condition can be silently dropped.
-/
import Mathlib

namespace ORRW

open Finset

/-- Sites of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) := Fin d → ℤ

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

/-- `E w k`: the set of undirected edges crossed in the first `k` steps.  This
is `E_k` of `orrw.tex`; `E w 0 = ∅`.

The `min k n` matters.  `edgeAt w i` for `i ≥ n` is the degenerate loop
`s(pos w n, pos w n)`, which the paper's
`E_n := {{X_{i-1}, X_i} : 1 ≤ i ≤ n}` never contains; without the `min`, the
bound `|E_k| ≤ d |R_k|` of `eq:edges-sites` is false.
For `k ≤ n`, which is the only range the step rule ever uses, `min k n = k`. -/
def E {d n : ℕ} (w : Fin n → Dir d) (k : ℕ) : Finset (Sym2 (Site d)) :=
  (range (min k n)).image (edgeAt w)

/-- `R w k`: the range `R_k = {X_0, …, X_k}` of `orrw.tex`. -/
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
/-- `ℙ_β` of an event depending on the first `n` steps.  Stated for a `Prop`
valued predicate so that no decidability hypothesis can quietly change the
event. -/
noncomputable def prb {d : ℕ} (n : ℕ) (β : ℝ) (P : (Fin n → Dir d) → Prop) : ℝ :=
  ∑ w : Fin n → Dir d, prob β w * (if P w then 1 else 0)

end ORRW
