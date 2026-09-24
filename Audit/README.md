# Audit Comparator Surface

This directory contains Mathlib-only comparator challenges for the four main
theorems of the formalization of *Once-reinforced random walk on `ℤ^d` has
range exponent at least `d/(d+1)`* (Ahmed Bou-Rabee and Yuval Peres): the
range lower bound, its stretched-exponential lower tail, the almost-sure bound
the paper draws from the tail, and the occupation measure bound.  Each
comparator lives in its own subdirectory:

| Directory | Paper statement | Checked theorem | Library theorem |
| --- | --- | --- | --- |
| `RangeLowerBound/` | Theorem 1.1, `thm:main` | `ORRWAudit.range_lower_bound` | `ORRW.range_lower_bound` |
| `RangeTail/` | Theorem 1.2, `thm:whp` | `ORRWAudit.range_tail` | `ORRW.range_tail` |
| `RangeAlmostSure/` | the almost-sure bound after Theorem 1.2 | `ORRWAudit.range_ae` | `ORRW.range_ae` |
| `OccupationMeasure/` | Theorem 1.3, `thm:occupation-intro` | `ORRWAudit.occupation_measure` | `ORRW.occupation_measure` |

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every
definition needed to read the theorem, states the theorem, and ends with one
`sorry`, the proof being checked.  The definitions form one vocabulary block,
between `-- VOCABULARY-BEGIN` and `-- VOCABULARY-END`, byte-identical in all
four challenges: the lattice `ℤ^d`, its `2d` directions and the position of a
direction word; the traversed edges `E_k`, the range `R_k` and the step rule
of once-reinforced random walk; its law on words of length `n`, with
expectation and probability; and its law on infinite direction words, built
from the one-step kernels by the Ionescu-Tulcea theorem.

## What Is Checked

Nothing is assumed.  The four theorems take no cited result as a hypothesis,
and neither do the challenges.

- **`RangeLowerBound`** (Theorem 1.1): for `d ≥ 2` there is `c > 0` such that
  `E_β |R_n| ≥ c β^{-d/(d+1)} n^{d/(d+1)}` for every `β ≥ 1` and every `n`.
- **`RangeTail`** (Theorem 1.2): for `d ≥ 2` there are `c, C > 0` such that
  `P_β(|R_n| < c β^{-d/(d+1)} n^{d/(d+1)}) ≤ exp(-c (n/β)^{(d-1)/(d+1)})` for
  every `β ≥ 1` and every `n ≥ C β`.
- **`RangeAlmostSure`** (after Theorem 1.2): for `d ≥ 2` there is `c > 0`
  such that for every `β ≥ 1`, almost surely,
  `|R_n| ≥ c β^{-d/(d+1)} n^{d/(d+1)}` for all large `n`.
- **`OccupationMeasure`** (Theorem 1.3): for `d ≥ 2` there is `C` such that
  `∑_{j<n} P_β(X_j = z) ≤ C β n^{1/(d+1)}` for every `β ≥ 1`, every `n ≥ 1`
  and every site `z`.

## Definition Provenance

The challenge definitions are statement-level copies of the repository
definitions needed to state the theorems, in the namespace `ORRWAudit`.  Five
of them copy definitions of the shared library Lattice-Probability that the
repository re-exports under the `ORRW` namespace; the vocabulary itself is
built on Mathlib alone.

| Challenge declaration | Repository source |
| --- | --- |
| `Site` | `LatticeProb/Site.lean` (Lattice-Probability), re-exported by `ORRW/Basic.lean` |
| `Dir`, `dirVec`, `pos`, `edgeAt` | `LatticeProb/Walk/Basic.lean` (Lattice-Probability), re-exported by `ORRW/Basic.lean` |
| `E`, `R`, `stepWeight`, `totalWeight`, `stepProb`, `prob`, `expect`, `prb` | `ORRW/Basic.lean` |
| `ofPrefix`, `ofPath`, `stepPMF`, `initPMF`, `stepMeasure`, `initMeasure`, `kappa`, `isMarkovKernel_kappa`, `instIsMarkovKernel_kappa`, `initTraj`, `pathMeasure` | `ORRW/Support/InfinitePath.lean` |
| `totalWeight_pos` | `ORRW/Support/Guards.lean` |

The vocabulary carries two lemmas, `totalWeight_pos` and
`isMarkovKernel_kappa`, because `pathMeasure` needs the one-step kernels to be
Markov kernels as an instance.  They are proofs, not definitions, and they
enter the statement only through that instance.

## Solutions

Each `Solution.lean` imports the repository together with
`Audit/Support/Vocabulary.lean`, a verbatim copy of the vocabulary block that
imports only Mathlib, and proves the byte-identical statement from the
corresponding theorem of `ORRW/MainTheorems.lean` through the identifications
in `Audit/Support/Bridge.lean` (see [`DESIGN.md`](DESIGN.md)).

`Audit/StatementRegression.lean` is a local check of the statement-identity
part of the comparator: it elaborates each statement in the challenge
environment (`Audit/Support/Statements.lean`, which imports only Mathlib and
the vocabulary), checks that each solution theorem has exactly that type and
mentions no constant of the repository namespace `ORRW` or of the library
namespace `LatticeProb`, and prints the axioms of each solution theorem.

## Reproducing The Checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and set `enable_nanoda: false`.  Each challenge elaborates standalone against
this repository's Mathlib toolchain, e.g.

```bash
bash Audit/check_standalone.sh Audit/RangeLowerBound/Challenge.lean
bash Audit/check_standalone.sh --vocabulary
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'`
warning per challenge; the second command checks that the vocabulary block is
the same in every challenge and in `Audit/Support/Vocabulary.lean`.  The
solutions and the regression build with

```bash
lake build Audit.StatementRegression
```

which prints, for each of the four theorems, that it is identical to the
challenge statement and depends only on `propext`, `Classical.choice` and
`Quot.sound`.

**Status.**  All four solutions build, and the statement regression and the
axiom prints pass locally.  `leanprover/comparator` was run on all four pairs
on 2026-09-24 at commit `8d0e8c3`, and each pair passed with the Lean kernel
and again with the independent nanoda kernel.
[`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md) records the results and the
reproduction steps.  The workflow
[`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml) runs
it on request.
