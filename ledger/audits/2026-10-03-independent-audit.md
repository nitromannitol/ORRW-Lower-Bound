# Independent refute-first audit — ORRW-Lower-Bound

Date: 2026-10-03.  Auditor: an independent instance, refute-first, read-only with respect to
the audited material; this note and the two state promotions it licenses are the only change
it makes.  Repo: `~/lean/ORRW-Lower-Bound`, `main` at the pinned commit, clean tree.

**Result: not refuted.  No FAIL.**  The paper pin, all 24 frozen hashes, the manifest↔tree
correspondence, all 24 axiom closures, the repo gates and the comparator runs pass.  Two
hygiene notes (H1, H2) below do not affect a statement, a proof or a closure.  The 24 nodes are
promoted `SEALED → PROVED`.

## What was checked, and how

1. **Paper pin.** `sha256(paper/orrw.tex)` recomputed with an independent script
   (`/tmp/orrw-audit/myhash.py`, Python `hashlib`) = `cd913b19…5781a`, equal to
   `source_pin.sha256`.
2. **Frozen hashes.** For each of the 24 nodes the bytes strictly between
   `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END` (one leading newline dropped) were
   hashed by the same independent script: **24/24 equal** to `frozen_sha256`, exactly one marker
   pair per file, and the declared export name occurs in the block.  A hash mismatch, an extra
   or missing marker, or a wrong name would have been a FAIL.
3. **Axiom closures.** `/tmp/orrw-audit/AuditAxioms.lean` is an independently written file that
   prints `#print axioms` for the 24 exports; every line is exactly
   `[propext, Classical.choice, Quot.sound]`, 24/24, with no `sorryAx` or other axiom.
4. **Gates.** `python3 tools/verify.py` → `verify: all checks passed`; `check_warnings` sees a
   warning-free 8726-job build; `check_axioms` reports all 24 clean; `certificate --check`
   matches.
5. **Comparator surface.** `ORRWAudit/COMPARATOR_RUNS.md` records `leanprover/comparator` on the
   four pairs (`RangeLowerBound`, `RangeTail`, `RangeAlmostSure`, `OccupationMeasure`) under the
   Lean kernel and the independent `nanoda` kernel, all passed.
6. **Correspondence.** The paper line anchors in `source:` resolve to labels (`check_coverage`,
   `paper_anchors`), and the formulation deltas are the ones recorded in
   [`../../VERIFICATION.md`](../../VERIFICATION.md) (constant convention, finite-vs-infinite
   paths, exit-time normalisation, effective resistance, supermartingale and occupation
   forms).  No node is refuted by those deltas; the constant convention and the weaker Cesàro
   form only weaken the Lean statements relative to the paper.

## Per-node table

`hash` is the independent recomputation of step 2, `ax` the closure of step 3.  All are PASS.

| id | export | paper | hash | ax |
|---|---|---|---|---|
| `thm-main` | `Frozen.range_lower_bound` | `orrw.tex:112-119` | ✔ | std |
| `thm-whp` | `Frozen.range_tail` | `orrw.tex:128-136` | ✔ | std |
| `lem-max-exit` | `Frozen.max_exit` | `orrw.tex:423-432` | ✔ | std |
| `lem-schur` | `Frozen.one_point_insertion` | `orrw.tex:447-468` | ✔ | std |
| `lem-packing` | `Frozen.resistance_packing` | `orrw.tex:485-492` | ✔ | std |
| `lem-insertion` | `Frozen.insertion_inequality` | `orrw.tex:515-523` | ✔ | std |
| `guard-total-weight-pos` | `Frozen.totalWeight_pos` | model guard | ✔ | std |
| `guard-prob-pmf` | `Frozen.sum_prob_eq_one` | model guard | ✔ | std |
| `guard-edges-le-sites` | `Frozen.card_edges_le_card_range` | `orrw.tex:723-725` | ✔ | std |
| `guard-one-step-witness` | `Frozen.expect_card_range_one_step` | numeric witness | ✔ | std |
| `lem-martingale` | `Frozen.supermartingale_drift` | `orrw.tex:596-599` | ✔ | std |
| `lem-walk-order` | `Frozen.insertion_order` | `orrw.tex:632-644` | ✔ | std |
| `prop-charge` | `Frozen.accumulated_charge` | `orrw.tex:669-676` | ✔ | std |
| `lem-exp` | `Frozen.time_versus_charge` | `orrw.tex:739-763` | ✔ | std |
| `prop-tail` | `Frozen.sigma_tail` | `orrw.tex:792-799` | ✔ | std |
| `prop-displacement` | `Frozen.displacement` | `orrw.tex:863-877` | ✔ | std |
| `prop-beta-sharp` | `Frozen.exponents_optimal` | `orrw.tex:912-922` | ✔ | std |
| `lem-green` | `Frozen.lazy_green_bounds` | `orrw.tex:991-1007` | ✔ | std |
| `thm-occupation` | `Frozen.occupation` | `orrw.tex:1039-1051` | ✔ | std |
| `thm-occupation-cesaro` | `Frozen.occupation_cesaro` | `orrw.tex:1102-1105` | ✔ | std |
| `thm-occupation-measure` | `Frozen.occupation_measure` | `orrw.tex:145-151` | ✔ | std |
| `bridge-path-measure` | `Frozen.pathMeasure_restr` | infrastructure | ✔ | std |
| `ae-range` | `Frozen.range_ae` | `orrw.tex:138-141` | ✔ | std |
| `ae-displacement` | `Frozen.displacement_ae` | closing display of `prop:displacement` | ✔ | std |

## Refute-first scope and limits

* The **finite guards** (`totalWeight_pos`, `sum_prob_eq_one`, `expect_card_range_one_step`,
  `card_edges_le_card_range`) and the one-point-insertion identities are finite identities; they
  are proved in the repository (`ORRW/Certificate.lean` prints their closures) and were read
  against their paper lines.  No counterexample was found.
* The **asymptotic bounds** have the shape `∃ c > 0, ∀ β ≥ 1, ∀ n, …`, so a finite simulation can
  exhibit no counterexample to the constant; the refutation attempt is against the *shape* and
  the paper reading, not against a number.  `prop-beta-sharp` is the sharpness statement that
  makes the exponent `d/(d+1)` optimal, and its two "no better exponent" clauses read correctly.
* The correspondence is as recorded in `VERIFICATION.md`; that note already states that the
  Lean kernel checks the statements and their proofs while matching them to the paper is a
  mathematical review, which this audit performed at the level of the anchors and formulation
  deltas.

## Hygiene notes

* **H1.** The two almost-sure corollaries `range_ae` and `displacement_ae` are not separate
  paper environments; their `source:` anchors point at prose after `thm:whp` and at the closing
  display of `prop:displacement`, which the rulings A-003/A-004 record.  No statement defect.
* **H2.** `thm-occupation-cesaro` freezes the weaker averaged Cesàro consequence rather than
  the paper's `eq:cesaro` sum; `VERIFICATION.md` records the delta and it only weakens the
  claim.

## Conclusion

Every registered node is sealed with a clean closure, the frozen surface is pinned and intact,
the gates and comparator runs pass, and no statement was refuted.  The audit licenses the
promotion of all 24 nodes from `SEALED` to `PROVED`.
