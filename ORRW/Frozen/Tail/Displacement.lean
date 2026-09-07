/-
Frozen statement of Proposition 6.1 of Bou-Rabee--Peres, *Once-reinforced random
walk on `ℤ^d` has range exponent at least `d/(d+1)`*, Section 6, Proposition
(Displacement and exit times), label `prop:displacement`, `orrw.tex:863-877`:

  "Let `d ≥ 2`.  There are constants `c > 0` and `C < ∞`, depending only on `d`,
   such that for every `β ≥ 1`,
     `E_β τ_{B_r} ≤ Cβ(2r+1)^{d+1}`  for every integer `r ≥ 0`,
   and
     `E_β Λ_n ≥ cβ^{-1/(d+1)}n^{1/(d+1)}`  for every integer `n ≥ 0`.
   Moreover, `P_β`-almost surely,
     `liminf_{n→∞} Λ_n n^{-1/(d+1)} ≥ cβ^{-1/(d+1)}`."

The two objects are those of `orrw.tex`:

  "the maximal displacement `Λ_n := max_{0≤k≤n} ‖X_k‖_∞` and the exit time
   `τ_{B_r} := inf{n ≥ 0 : X_n ∉ B_r}` of the box `B_r := [-r,r]^d ∩ Z^d`."

Modelling decisions.

* Ruling F-621 (`E_β τ` is the supremum of its finite-horizon truncations).
  Under ruling R-001 there is no measure on infinite paths, and `τ_{B_r}` is
  unbounded, so `E_β τ_{B_r}` is not a term.  What is frozen is the bound on
  every truncation `E_β[τ_{B_r} ∧ N]`, uniformly in the horizon `N`, which is
  equivalent by monotone convergence and is what the paper's own proof
  establishes.

* Ruling F-622 (the truncated exit time as a sum of survival probabilities).
  `τ ∧ N = ∑_{m<N} 1_{{τ > m}}`, and `{τ_{B_r} > m}` is the event that the walk
  has stayed in the box through time `m`, that is `‖X_j‖_∞ ≤ r` for every
  `j ≤ m`.  The left-hand side below is therefore `E_β[τ_{B_r} ∧ N]` written as
  `∑_{m<N} P_β{‖X_j‖_∞ ≤ r for all j ≤ m}`.  This uses `ORRW.prb`, which takes a
  `Prop`-valued event (ruling R-003), so no decidability instance enters and no
  junk value of an infimum can appear.

* Ruling F-623 (`B_r` is a sup-norm ball).  `x ∈ B_r = [-r,r]^d ∩ Z^d` is
  `‖x‖ ≤ r` for the Pi sup norm on `ORRW.Site d = Fin d → ℤ`, the same norm as
  in `ORRW.Frozen.potential_kernel_exists`.

* Ruling F-624 (`Λ_n` is a `Finset.sup'`).  The maximum over `0 ≤ k ≤ n` is
  `(Finset.range (n+1)).sup'`, whose nonemptiness witness is
  `Finset.nonempty_range_add_one`; no `OrderBot` on `ℝ` is needed and the maximum
  is genuinely attained.

* Ruling F-625 (the almost sure clause is not frozen).  The `liminf` assertion
  is a statement about the infinite path, which ruling R-001 excludes: it is the
  Borel--Cantelli consequence of `thm:whp`, whose own almost sure form is
  likewise outside the frozen surface (see `ORRW/Frozen/RangeTail.lean`, which
  freezes only the finite-`n` tail).  The two displayed bounds are frozen; the
  `liminf` clause is recorded here as deliberately omitted.

* Ruling F-626 (order of quantifiers, positivity, exponents).  `c` and `C`
  depend only on `d`, so they are bound before `β`, `r`, `N` and `n`; both are
  asserted positive; `β^{-1/(d+1)}` and `n^{1/(d+1)}` are `Real.rpow` powers,
  while `(2r+1)^{d+1}` is a natural power.
-/
import ORRW.Lattice
import ORRW.Support.Displacement

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.displacement (d : ℕ) (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ β : ℝ, 1 ≤ β →
      (∀ r N : ℕ,
          ∑ m ∈ Finset.range N,
              ORRW.prb (d := d) N β (fun w => ∀ j ≤ m, ‖ORRW.pos w j‖ ≤ (r : ℝ))
            ≤ C * β * (2 * (r : ℝ) + 1) ^ (d + 1)) ∧
      (∀ n : ℕ,
          c * β ^ (-((1 : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1))
            ≤ ORRW.expect (d := d) n β
                (fun w => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
                  (fun k => ‖ORRW.pos w k‖)))
-- FROZEN-STATEMENT-END
:= ORRW.Support.displacement_of hd
