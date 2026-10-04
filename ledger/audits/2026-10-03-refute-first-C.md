# Independent refute-first audit — ORRW-Lower-Bound, Batch C

Auditor role: independent second-key audit, refute-first. Read-only in the repository; this file
is the only thing written. No `git add/commit/push`, no `lake build` invoked directly.

## Head commit read

* `git rev-parse HEAD` when the audit began: `492a2361b02f9e90ee0f763ee1638b3089ee2c57`
  (the brief's pin).
* `git rev-parse HEAD` at report time: `cdd3e86b81fb41b24fa7f33cffc09601bd2aef4b`.
  Between the two calls a concurrent audit landed (manifest mtime `2026-10-03 23:25:16`, new file
  `ledger/audits/2026-10-03-independent-audit.md`) and the manifest now marks **all 24 nodes
  `PROVED`**. The frozen file bytes (mtimes `2026-09-23`) and `paper/orrw.tex` are unchanged, and
  the manifest's `frozen_sha256` / `source_pin` are unchanged, so the frozen contract audited
  below is the one at the pin. See "What I could not verify" for the residual risk.
* `python3 tools/check_manifest.py` (current tree): `check_manifest: OK (24 nodes, 0 unsealed;
  closure 0 checked, 24 skipped; 41 ORRW declarations indexed)`. It re-checks
  `sha256(paper/orrw.tex)` against `source_pin`.

## Verdicts

| node | verdict | evidence |
|---|---|---|
| `guard-one-step-witness` | PASS | `frozen_sha256` recomputed `a87315d1…` = manifest; block has no `axiom/native_decide/set_option/sorry`; arithmetic of the witness independently checked (4 directions × `|R_1|=2` × `1/4 = 2`); `β=1` inhabits `hβ`; closure `[propext, Classical.choice, Quot.sound]`. |
| `lem-martingale` | CONCERN | Frozen is the paper's `eq:drift`, not the lemma's supermartingale conclusion. Hash `0fcbbac…` matches; drift direction/constant `≥1` correct; `mu>0` proved; closure clean; hypotheses `1≤d, 1≤β, m, v : Fin m → Dir d` are satisfiable. Recorded ruling F-501/F-502/F-503 and `VERIFICATION.md` cover the modelling. |
| `lem-walk-order` | PASS | Frozen literally states the paper's `M≤k+1`, an enumeration of `V=R_{σ_k}`, clauses (i)/(ii) and distinctness. Hash `7fb55dd…` matches; event `{σ_k<∞}` rendered as `hfin : k ≤ (E w n).card` (F-511, via `sigma_le_iff`); `d=1`, word of `k` right-steps satisfies `hk`/`hfin`; closure clean. |
| `prop-charge` | PASS | Paper `Γ_n ≤ Cβ|E_n|^{1+1/d}`; frozen `∃K, 0<K ∧ ∀β≥1 ∀n ∀w:Fin n ∀m, Gamma β w m ≤ Kβ((E w m).card)^(1+1/d)`. `K` bound before `β` (F-522), exponent exact, `m>n` constant (F-523), "a.s."→"every word" is the stronger reading (F-521). Hash `8e68e42…`; closure clean; `d≥2` satisfiable. |
| `lem-exp` | CONCERN | Statement and both conclusions (`E e^{θ(N∧ζ)/2} ≤ e^{2θb}`, `P{4b+s≤N∧ζ} ≤ e^{-θs/2}`, `θ=1/[4(1+p+q)]`) match the paper; but `hχ` is the only hypothesis not passed to the prover (see below), and the stopping-time/filtration content is the abstract encoding F-601…F-606 rather than Mathlib's `Supermartingale`. Hash `b967a0c…`; closure clean; hypotheses inhabited by the `prop-tail` instantiation (`sigma_tail_of`). |
| `prop-tail` | CONCERN | Exponents `8Kβk^{1+1/d}` and `k^{(d-1)/d}` match; but the paper has a single `C≥1` used in *both* `8C` and `C^{-1}`, the Lean has independent `∃c,K`, and the header comment misquotes the paper (see below). Logically equivalent under the recorded constant convention (`VERIFICATION.md` §Constants); hash `399916e…`; closure clean; `d≥2` satisfiable. |

Axiom closure quoted for every node (from `tools/check_warnings.py`, lines `ORRW/Certificate.lean:40-45`):

```
ORRW/Certificate.lean:40:0: 'ORRW.Frozen.expect_card_range_one_step' depends on axioms: [propext, Classical.choice, Quot.sound]
ORRW/Certificate.lean:41:0: 'ORRW.Frozen.supermartingale_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
ORRW/Certificate.lean:42:0: 'ORRW.Frozen.insertion_order' depends on axioms: [propext, Classical.choice, Quot.sound]
ORRW/Certificate.lean:43:0: 'ORRW.Frozen.accumulated_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
ORRW/Certificate.lean:44:0: 'ORRW.Frozen.time_versus_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
ORRW/Certificate.lean:45:0: 'ORRW.Frozen.sigma_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Integrity / gates (exact commands and output)

Independent frozen-hash recomputation over the exact bytes (one leading newline dropped), plus a
banned-token scan of each block, gave `sha_ok=True banned=[]` for all six nodes.

```
$ python3 tools/check_manifest.py
check_manifest: OK (24 nodes, 0 unsealed; closure 0 checked, 24 skipped; 41 ORRW declarations indexed)

$ python3 tools/check_axioms.py
check_axioms: OK (24 exports; only propext, Classical.choice, Quot.sound)

$ python3 tools/verify.py
... (all sub-checks OK)
verify: all checks passed
```

No `axiom`, `native_decide`, `set_option` or `sorry` token occurs inside any of the six frozen
blocks. There is no `External` and no `DRAFT_SORRY` node anywhere; all manifest `provider` fields
equal the corresponding `export`, so no node is conditional on an assumed predecessor.
Standalone `tools/check_axioms.py` first failed only because `.olean`s for
`ORRW.Frozen.Guards.OneStepWitness` and `ORRW.Frozen.AlmostSure.DisplacementAlmostSure` had not
been built; `tools/verify.py` (via `check_warnings`) performed the 8726-job build, after which
`check_axioms` passed.

## CONCERN details

### C1. `lem-exp` — unused `hχ`

Paper line (`orrw.tex:744`): "and let `\zeta` be a stopping time for this filtration."
Lean binder (`ORRW/Frozen/Tail/TimeVersusCharge.lean:78`):
`(hχ : ∀ (m : ℕ) (v : Fin m → Dir d), χ m v ≤ 1)`
The prover call at line 115 is
`ORRW.timeCharge_mgf hdpos hβ Φ Γ ζ χ p q b θ hθpos hθp hθq hζ0 hΦ0 hΓ0 hζ hΦ hδ hΓ hdrift N`
and `hχ` is absent; the file's own comment (lines 67-69) says "it never appeals to `hχ`. The unused
binder is retained in the frozen statement." `hχ` therefore is not EXCESS in the sense of a
non-paper hypothesis: together with `hζ0`/`hζ` it is the F-604 encoding of "`ζ` is a stopping
time", and the paper's `χ=1_{n<ζ}` satisfies it. It is non-blocking but is a deviation from the
minimal paper hypothesis set.

Smallest reproducer:
```
$ grep -n 'hχ' ORRW/Frozen/Tail/TimeVersusCharge.lean
45:  satisfies `hζ0`, `hχ` and `hζ` ...
67:/- A truncated stopping time has increments in `{0,1}`, giving `hχ`.
69:appeals to `hχ`.  The unused binder is retained in the frozen statement. -/
78:    (hχ : ∀ (m : ℕ) (v : Fin m → Dir d), χ m v ≤ 1)
$ sed -n '115p' ORRW/Frozen/Tail/TimeVersusCharge.lean
    ORRW.timeCharge_mgf hdpos hβ Φ Γ ζ χ p q b θ hθpos hθp hθq hζ0 hΦ0 hΓ0 hζ hΦ hδ hΓ hdrift N
```

### C2. `prop-tail` — two constants + header misquote

Paper lines (`orrw.tex:793-797`):
```
793:  Let $d\geq2$. There is a constant $C\geq1$, depending only on $d$, such
796:  $\P_\beta\{\sigma_k>8C\beta k^{1+1/d}\}$
797:  $\leq\exp(-C^{-1}k^{(d-1)/d})$
```
Lean frozen binders (`ORRW/Frozen/Tail/SigmaTail.lean`, inside the block):
`∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ β : ℝ, 1 ≤ β → ∀ k : ℕ, 1 ≤ k → ∀ N : ℕ,
  8 * K * β * (k : ℝ) ^ (1 + (1 : ℝ) / (d : ℝ)) ≤ (N : ℝ) → prb … ≤ Real.exp (-(c * (k : ℝ) ^ (((d : ℝ) - 1) / (d : ℝ))))`.
The paper's single `C` (in `8C` and `C⁻¹`) is split into independent `c,K`; the `∀N` with
`threshold ≤ N` is the F-612 finite-horizon device. The two forms are logically equivalent:
taking `c=1/C, K=C` gives the Lean form, and conversely `C=max(K,1/c,1)` recovers the paper's
single-constant display (the threshold raises and the event shrinks, while `c≥1/C` weakens the
exponential). `VERIFICATION.md` §Constants records this convention. However, the frozen file's
header comment (lines 7-10) *quotes* the paper as "let `K` be the constant of Proposition
`prop:charge`. There is `c > 0` …", which is not what `orrw.tex:792-799` says; the comment should be
corrected to the actual single-`C` display. Non-blocking for the statement because of the
equivalence above.

Smallest reproducer:
```
$ awk 'NR>=792 && NR<=799 {printf "%d: %s\n", NR, $0}' paper/orrw.tex
792: \begin{proposition}[Tail of $\sigma_k$]\label{prop:tail}
793:   Let $d\geq2$. There is a constant $C\geq1$, depending only on $d$, such
794:   that for every $\beta\geq1$ and every integer $k\geq1$,
795:   \[
796:     \P_\beta\bigl\{\sigma_k>8C\beta k^{1+1/d}\bigr\}
797:     \leq\exp\bigl(-C^{-1}k^{(d-1)/d}\bigr)\, .
798:   \]
799: \end{proposition}
$ sed -n '7,10p' ORRW/Frozen/Tail/SigmaTail.lean
  "Let `d ≥ 2` and let `K` be the constant of Proposition `prop:charge`.  There
   is `c > 0`, depending only on `d`, such that for every `β ≥ 1` and every
   integer `k ≥ 1`,
     `P_β{σ_k > 8Kβk^{1+1/d}} ≤ exp(-ck^{(d-1)/d})`."
```

### Note on `lem-martingale`

The paper's lemma conclusion is "`(n+Φ_n−Γ_n)` is a supermartingale"; the frozen block is the
paper's own `eq:drift` `E_β[Γ_{n+1}−Γ_n−(Φ_{n+1}−Φ_n)|F_n] ≥ 1`, with the conditional average
written as `∑_a stepWeight β v m a * (…) / mu β v m`. This is the statement the paper proves and
calls "the assertion", and `VERIFICATION.md` §Differences records that Lemma 3.1 is expressed as
the one-step conditional drift on each finite history under R-001. Sign, the constant `1`,
`mu>0` (via `totalWeight_pos`), and non-vacuity (`d=1, β=1, m=0`) all check. Recorded as CONCERN
only because the literal conclusion is the one-step drift rather than the infinite-horizon
process statement.

## What I could not verify

* The frozen tree was not audited at the literal pin `492a236`: by report time `HEAD` is
  `cdd3e86` and the manifest marks all nodes `PROVED`. Frozen file bytes, `paper/orrw.tex` and the
  manifest's `frozen_sha256`/`source_pin` are unchanged, and every batch-C hash still matches the
  current manifest, so the statements audited are the pinned ones; but I cannot rule out that the
  concurrent promotion touched something outside the six blocks I hashed.
* No node carries `closure_sha256`, so `check_manifest` reports `closure 0 checked, 24 skipped`.
  The source-level dependency-closure tripwire (its own docstring says it is "a conservative …
  heuristic, not an elaboration-equivalent dependency oracle") was therefore not exercised; I
  verified frozen bytes and Lean axiom closures, not that heuristic hash.
* I did not audit batches A, B, D beyond the dependency references of batch C
  (`insertion_inequality`, `max_exit`, `accumulated_charge`, `supermartingale_drift`).
* The paper's infinite-horizon measure-theoretic supermartingale statement is represented by its
  finite-history drift equivalent; I checked the equivalence argument, not a Mathlib
  `MeasureTheory.Supermartingale` object.
* The equivalence of the two-constant `prop-tail` form with the paper's single-`C` form is a
  pencil argument (given above), not machine-checked.

## Conclusion

No FAIL was found in Batch C: all six nodes are fully proved with closure exactly
`{propext, Classical.choice, Quot.sound}`, the frozen bytes match the manifest and faithfully
carry the cited paper content, and the hypotheses are inhabited; the only findings are the two
documented, non-blocking CONCERNs (`lem-exp`'s unused `hχ`; `prop-tail`'s split constants plus a
header misquote to be corrected), so every assigned node may be promoted `SEALED → PROVED`
(and at report time all six are already marked `PROVED`).
