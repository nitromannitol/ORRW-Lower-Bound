# Independent refute-first audit — ORRW-Lower-Bound, Batch A

* **Auditor:** DeepSeek fleet, second-key audit (independent; wrote none of the development).
* **Batch:** A — `thm-main`, `thm-whp`, `ae-range`, `ae-displacement`, `bridge-path-measure`, `lem-max-exit`.
* **Repository:** `~/lean/ORRW-Lower-Bound`
* **Head read:** `492a2361b02f9e90ee0f763ee1638b3089ee2c57` (`git rev-parse HEAD`, read-only).
* **Paper pin:** `paper/orrw.tex`, sha256 `cd913b195b6a2e4992eae367952beaba3a065ff2b0e7aaa9b794ab69e7b5781a` (matches `ledger/manifest.yaml:source_pin`).
* **Constraint observed:** no `git add/commit/push`, no `lake build`, no file edited except this report.

## Gate results (machine-checked, exact commands)

```
$ python3 tools/check_manifest.py
check_manifest: OK (24 nodes, 0 unsealed; closure 0 checked, 24 skipped; 41 ORRW declarations indexed)

$ python3 tools/check_axioms.py
check_axioms: OK (24 exports; only propext, Classical.choice, Quot.sound)

$ python3 tools/verify.py
... (all sub-checks OK) ...
verify: all checks passed

$ python3 tools/check_coverage.py
check_coverage: 16 statements in the paper, 16 represented in the manifest
every theorem, lemma and proposition in the paper is represented in the manifest

$ python3 tools/paper_citations.py
paper_citations: 16 correct, 0 stale, 0 not anchored to a label, 0 unresolvable

$ python3 tools/check_clauses.py     -> OK (18 statements, each has a recorded correspondence note; 13 heuristic "paper asserts more", all explained)
$ python3 tools/check_constants.py   -> OK (24 statements; every existential constant is bound before β, n, k, m and h)
$ python3 tools/check_exponents.py   -> OK (19 statements; every paper exponent appears in its Lean statement or is explained)
```

Per-node axiom closures (from `tools/check_warnings.py` replaying `ORRW/Certificate.lean`; identical to `check_axioms`):

```
info: ORRW/Certificate.lean:31:0: 'ORRW.Frozen.range_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ORRW/Certificate.lean:32:0: 'ORRW.Frozen.range_tail'        depends on axioms: [propext, Classical.choice, Quot.sound]
info: ORRW/Certificate.lean:33:0: 'ORRW.Frozen.max_exit'           depends on axioms: [propext, Classical.choice, Quot.sound]
info: ORRW/Certificate.lean:52:0: 'ORRW.Frozen.pathMeasure_restr'  depends on axioms: [propext, Classical.choice, Quot.sound]
info: ORRW/Certificate.lean:53:0: 'ORRW.Frozen.range_ae'            depends on axioms: [propext, Classical.choice, Quot.sound]
info: ORRW/Certificate.lean:54:0: 'ORRW.Frozen.displacement_ae'    depends on axioms: [propext, Classical.choice, Quot.sound]
check_warnings: OK (0 registered sorry warnings)
```

Independent recomputation of each assigned frozen block (bytes between `BEGIN`/`END`, one leading newline dropped) reproduced the manifest SHA-256 exactly, and found **no** `axiom`, `admit`, `sorryAx`, `native_decide`, `set_option`, or `sorry` token inside any block:

| node | block bytes | recomputed SHA-256 (16) | manifest match | banned tokens |
|---|---|---|---|---|
| `thm-main` | 259 | `e9eed22a4b1d0fd1` | ✅ | none |
| `thm-whp` | 367 | `230e9100dfb1799b` | ✅ | none |
| `lem-max-exit` | 296 | `a08d37bbdb7da7a3` | ✅ | none |
| `ae-range` | 318 | `05b123b0cea38046` | ✅ | none |
| `ae-displacement` | 399 | `881214fda81b58cf` | ✅ | none |
| `bridge-path-measure` | 250 | `2d801141e36364b1` | ✅ | none |

Production-tree scan: no `axiom`, `constant`, `admit`, `sorryAx`, `unsafe`, `native_decide`, `@[extern]`, `implemented_by`; no `External` anywhere; `sorry` count 0. `set_option`s in the assigned files (`maxHeartbeats` in `RangeAlmostSure.lean:33`, `DisplacementAlmostSure.lean:27`) are **outside** the frozen blocks. Manifest has 0 `DRAFT_SORRY` / `CONDITIONAL` nodes; every provider in the dependency closure is `SEALED`.

## Verdict table

| node | verdict | evidence |
|---|---|---|
| `thm-main` | **PASS** | paper 112–119 quoted below; block hash ✅; closure `{propext, Classical.choice, Quot.sound}`; not vacuous (`d=2, n=1` gives `E\|R_1\|=2` via `guard-one-step-witness`) |
| `thm-whp` | **PASS** | paper 128–136 quoted below; hash ✅; closure ✅; equivalence of the two-constant form noted; not vacuous |
| `lem-max-exit` | **PASS** | paper 423–432 quoted below; hash ✅; closure ✅; `u/h/T` match `Dirichlet.lean`; non-junk via `dirichletLaplacian_isUnit`; `A={0}, d=1` gives `u=1/2` |
| `ae-range` | **PASS** | paper 138–141 quoted below; hash ✅; closure ✅; `pathMeasure` proved a probability measure (`isProbabilityMeasure_pathMeasure`); stronger eventual form noted |
| `ae-displacement` | **PASS** | paper 875–876 quoted below; hash ✅; closure ✅; `Λ_n` is `sup' (range (n+1)) ‖pos‖` with `‖·‖` the Pi sup-norm; stronger eventual form noted |
| `bridge-path-measure` | **PASS** | not a paper statement (manifest); hash ✅; closure ✅; identity is the correct `(n+1)`-letter marginal; not vacuous (`pathMeasure` is a probability measure) |

No node is conditional on an `External` or on a `DRAFT_SORRY` predecessor. No node takes a cited paper result as a hypothesis.

## Per-node source-fidelity detail

### `thm-main` — `ORRW.Frozen.range_lower_bound`, `ORRW/Frozen/RangeLowerBound.lean:18-21`
Paper `paper/orrw.tex:112-119`:
> "Theorem (Range lower bound) Let $d\geq2$. There is a constant $C\geq1$, depending only on $d$, such that for every $\beta\geq1$, $\E_\beta|R_n|\geq C^{-1}\beta^{-\frac{d}{d+1}}n^{\frac{d}{d+1}}$ for every $n\geq0$."

Lean:
```
theorem ... (d : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ,
      c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))
        ≤ ORRW.expect (d := d) n β (fun w => ((ORRW.R w n).card : ℝ))
```
Hypotheses/quantifier order/exponents/conclusion all faithful: `c` is bound after `d` and before `β,n` (depends only on `d`), events use `R w n = {X_0,…,X_n}` and `expect` is the finite-word expectation. Constant: Lean's `c` is the paper's `C^{-1}`; Lean asserts only `0 < c` where the paper has `C ≥ 1`, which is equivalent because the left side is monotone in `c` (replace `c` by `min c 1`; conversely the paper's `C` can be taken `max (1, 1/c)`). This is the recorded constant convention (`VERIFICATION.md` §Constants). No EXCESS binder.

### `thm-whp` — `ORRW.Frozen.range_tail`, `ORRW/Frozen/RangeTail.lean:20-25`
Paper `paper/orrw.tex:128-136`:
> "There is a constant $C\geq1$, depending only on $d$, such that for every $\beta\geq1$ and every $n$ with $n/\beta\geq C$, $\P_\beta\{|R_n|<C^{-1}\beta^{-\frac{d}{d+1}}n^{\frac{d}{d+1}}\}\leq\exp\bigl(-C^{-1}(n/\beta)^{(d-1)/(d+1)}\bigr)$."

Lean:
```
∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, C * β ≤ (n : ℝ) →
  ORRW.prb ... (fun w => ((ORRW.R w n).card : ℝ)
        < c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)))
    ≤ Real.exp (-(c * ((n : ℝ) / β) ^ (((d : ℝ) - 1) / ((d : ℝ) + 1))))
```
Hypotheses (`d≥2`, `β≥1`, `C*β ≤ n`) match `n/β ≥ C` since `β>0`; the event has the paper's strict `<`; the exponents `-d/(d+1), d/(d+1), (d-1)/(d+1)` match exactly; `c` occurs in both the event and the exponential as the paper's `C^{-1}` does. **Note (documented convention):** the paper uses a single `C` for the threshold and for `C^{-1}` in the bound, whereas Lean uses an independent threshold `C` and offset `c`. The two forms are logically equivalent: given Lean's `c,C`, set `C' := max (C, 1, 1/c)`; then `n/β ≥ C' ⇒ Cβ ≤ n` and `C'^{-1} ≤ c`, so the paper's event is contained and the exponent is dominated. No EXCESS binder.

### `lem-max-exit` — `ORRW.Frozen.max_exit`, `ORRW/Frozen/Insertion/ExitTimeBounds.lean:37-41`
Paper `paper/orrw.tex:423-432`:
> "Let $d\geq1$. Every finite nonempty $A\subset\Z^d$ satisfies $\max_{x\in A}u_A(x)\leq C|A|^{2/d}$, $\max_{x\notin A}h_A(x)\leq C|A|^{2/d}$, $T(A)\leq C|A|^{1+2/d}$."

Lean:
```
theorem ... {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Finset (Site d), A.Nonempty →
      (∀ x ∈ A, u A x ≤ C * (A.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ∧
      (∀ x ∉ A, h A x ≤ C * (A.card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ∧
      T A ≤ C * (A.card : ℝ) ^ (1 + (2 : ℝ) / (d : ℝ))
```
`C` is bound after `d` and before `A` (ruling F-101; otherwise trivial). The two maxima are rendered as universal bounds over `x∈A` / `x∉A` (ruling F-102) — equivalent because `u`/`h` are finite and the relevant `x` for `max_{x∉A}` ranges over finitely many neighbours of a finite `A`. Exponents and the three conjuncts match. `u,h,T` in `LatticeProb/Walk/Dirichlet.lean` are exactly the paper's `u_A=-Δ_A^{-1}1_A`, `h_A(x)=1+Σ_{y∈A,y∼x}u_A(y)`, `T(A)=Σ_{x∈A}u_A(x)`. No EXCESS binder.

### `ae-range` — `ORRW.Frozen.range_ae`, `ORRW/Frozen/AlmostSure/RangeAlmostSure.lean:35-39`
Paper `paper/orrw.tex:138-141`:
> "The right-hand side is summable in $n$ for each fixed $\beta$, so the Borel--Cantelli lemma gives the almost sure bound $\liminf_{n\to\infty}|R_n|n^{-\frac{d}{d+1}}\geq C^{-1}\beta^{-\frac{d}{d+1}}$."

Lean:
```
theorem ... {d : ℕ} [hd0 : Fact (0 < d)] (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 1 ≤ β),
      ∀ᵐ ω ∂(@ORRW.pathMeasure d hd0 β ⟨hβ⟩), ∀ᶠ n : ℕ in atTop,
        c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))
          ≤ ((ORRW.R (ORRW.ofPath n ω) n).card : ℝ)
```
Constants and exponents match. **Note (ruling A-003, documented):** the paper's `liminf` is rendered as an eventual lower bound `∀ᶠ n, cβ^{-e}n^{e} ≤ |R_n|`. This is *stronger* than the paper's display (eventual `≥ A` implies `liminf ≥ A`; the converse fails), so proving it establishes the paper's stated claim; it is not a weakening. `pathMeasure` is the genuine infinite-step ORRW law (its finite marginals are `ORRW.prob` by `bridge-path-measure`). Binder `[hd0 : Fact (0<d)]` is TYPING (needed by `Kernel.traj`/`pathMeasure`; derivable from `hd`), not EXCESS.

### `ae-displacement` — `ORRW.Frozen.displacement_ae`, `ORRW/Frozen/AlmostSure/DisplacementAlmostSure.lean:29-34`
Paper `paper/orrw.tex:875-876`, closing display of `prop:displacement`:
> "Moreover, $\P_\beta$-almost surely, $\liminf_{n\to\infty}\Lambda_nn^{-1/(d+1)}\geq C^{-1}\beta^{-1/(d+1)}$."

Lean:
```
theorem ... {d : ℕ} [hd0 : Fact (0 < d)] (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (β : ℝ) (hβ : 1 ≤ β),
      ∀ᵐ ω ∂(@ORRW.pathMeasure d hd0 β ⟨hβ⟩), ∀ᶠ n : ℕ in atTop,
        c * β ^ (-((1 : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) + 1))
          ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
              (fun k => ‖ORRW.pos (ORRW.ofPath n ω) k‖)
```
`Λ_n = max_{0≤k≤n}‖X_k‖_∞` is exactly `sup' (range (n+1)) (fun k => ‖pos (ofPath n ω) k‖)`: `range (n+1) = {0,…,n}` and `‖·‖` on `Site d = Fin d → ℤ` is the Pi/sup norm (`norm_le_pi_norm`), i.e. `‖·‖_∞`. Same ruling-A-003 strengthening as `ae-range` (documented, implies the paper's liminf). Binder `[hd0 : Fact (0<d)]` is TYPING, not EXCESS. The proof derives it from `range_ae` and `card_pathRange_le_originBox` (paper's `eq:range-box`), as the paper says.

### `bridge-path-measure` — `ORRW.Frozen.pathMeasure_restr`, `ORRW/Frozen/AlmostSure/PathMeasureBridge.lean:34-37`
Manifest source: "not a paper statement; required for the almost-sure corollaries (see CORRESPONDENCE.md, R-001 scope)". No paper line to compare. Lean:
```
theorem ... {d : ℕ} [Fact (0 < d)] {β : ℝ} [Fact (1 ≤ β)]
    (n : ℕ) (x : Π _i : Finset.Iic n, ORRW.Dir d) :
    ORRW.pathMeasure (d := d) β {ω | ORRW.restr n ω = x}
      = ENNReal.ofReal (ORRW.prob β (ORRW.ofPrefix n x))
```
`restr n` fixes the `n+1` letters `0..n`; `ofPrefix n x : Fin (n+1) → Dir d`; thus the RHS is `prob` of the `(n+1)`-letter word. This is exactly the finite-dimensional marginal identity the two almost-sure nodes need. The `Fact` binders are TYPING/STANDING for `Kernel.traj`, not EXCESS. Proof uses `pathMeasure_restr_eq_bind` (Ionescu–Tulcea) and `bind_partialTraj_eval` (induction matching `prob_succ`), both proved.

## Non-vacuity evidence

* The model-level guards are machine-checked frozen nodes: `guard-total-weight-pos` (`0 < totalWeight`), `guard-prob-pmf` (`Σ prob = 1`), `guard-edges-le-sites` (`|E| ≤ d|R|`), `guard-one-step-witness` (`expect (d:=2) 1 β |R_1| = 2` for every `β ≥ 1`). These certify that `prob` is a genuine pmf and `expect`/`prb` are not the zero functional, so `thm-main`/`thm-whp` are not vacuous. The witness `d=2, n=1, β≥1` inhabits `thm-main`'s hypothesis `d≥2, β≥1, n=0`.
* `ae-range`/`ae-displacement` use `ORRW.pathMeasure`; `isProbabilityMeasure_pathMeasure` (Support/AlmostSure.lean) proves it is a probability measure, so the `∀ᵐ` statements are not vacuous; `pathMeasure` is built from a Markov kernel whose normalisation is `guard-prob-pmf`.
* `lem-max-exit`: the library proves `dirichletLaplacian_isUnit`, ruling out the junk `Matrix.inv = 0` that would make `u ≡ 0`; e.g. `d=1, A={0}` gives `Δ_A=-2`, `u A 0 = T A = 1/2`, so the conclusion is non-junk. `A.Nonempty` is satisfiable for every `d ≥ 1`.
* `bridge-path-measure`: `pathMeasure` is a probability measure and the cylinders `{restr n = x}` partition the sample space, matching the pmf `prob` on the right.

## Deviations recorded (none are refutations)

1. **`thm-whp` two-constant form** (paper single `C` vs Lean `∃ c C`). Mathematically equivalent by `C' = max(C, 1, 1/c)`; recorded in `VERIFICATION.md` §Constants. Exact paper line: 129–134; exact Lean binder: line 21 `∃ c C : ℝ, 0 < c ∧ 0 < C ∧ …`.
2. **`ae-range` / `ae-displacement` eventual-vs-liminf** (ruling A-003). The Lean conclusion is strictly stronger and implies the paper's liminf. Exact paper lines: 139–140 and 875–876; exact Lean binder: `∀ᶠ n : ℕ in atTop, …` (RangeAlmostSure.lean:37; DisplacementAlmostSure.lean:31).
3. **`thm-main` `c>0` vs paper `C≥1`.** Equivalent as above; recorded convention. Exact paper line: 113; exact Lean binder: `∃ c : ℝ, 0 < c ∧ …` (RangeLowerBound.lean:19).

## What I could not verify

* I cannot machine-check that LaTeX prose semantics equals the Lean statement; `check_clauses`/`check_constants`/`check_exponents` are heuristic review aids, and `VERIFICATION.md` explicitly says "These checks do not prove equivalence between LaTeX and Lean statements." My source-fidelity findings rest on hand comparison against the quoted lines and on the recorded rulings (F-101/F-102/F-103, A-002/A-003/A-004, R-001/R-006 and the constants convention).
* The equivalence arguments in "Deviations" are ordinary mathematics, not formalized in Lean; they are one-line, but I did not formalize them.
* I did not run `lake build` (per instructions) and did not build the non-default `ORRWAudit` comparator target; the comparator restatements were read as corroboration only, not machine-checked in this run.
* I did not independently verify the *content* of the upstream `LatticeProb` library beyond the definitions used (`u`, `h`, `T`, `Dirichlet`, `exit_time_bounds`, `card_pathRange_le_originBox`, `pos`, norm lemmas); the axiom audit covers its transitive use.
* The brief's suggested `python3 tools/check_manifest.py .` fails with `unrecognized arguments: .` (the tool takes `--emit` only and resolves the repo root itself); the correct invocation is `python3 tools/check_manifest.py`, which was used.

## Conclusion

**All six Batch-A nodes can be promoted `SEALED -> PROVED`:** every frozen block matches its manifest hash, is proved with axiom closure exactly `{propext, Classical.choice, Quot.sound}` and no `sorryAx`, is non-vacuous, and faithfully formalizes the cited paper claim up to three explicitly documented, equivalence- or strengthening-preserving reformulations (single-vs-two constants in `thm-whp`; eventual-vs-liminf in `ae-range`/`ae-displacement`; `c>0`-vs-`C≥1` in `thm-main`) that all imply the paper's stated bounds.
