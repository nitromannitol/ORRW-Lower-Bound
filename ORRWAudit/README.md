# ORRWAudit Comparator Surface

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

Each pair has four files: `Challenge.lean`, `SolutionBasic.lean`, `Solution.lean` and
`comparator.json`.  `SolutionBasic.lean` is a verbatim, mechanical copy of the vocabulary block
of the pair's `Challenge.lean`, and imports only Mathlib.  `Solution.lean` imports the
repository together with the pair's `SolutionBasic.lean` and its bridge
`ORRWAudit/Support/<Pair>Bridge.lean`, and proves the byte-identical statement from the
corresponding theorem of `ORRW/MainTheorems.lean` (see [`DESIGN.md`](DESIGN.md)).  The
comparator checks each solution statement against its challenge, and the dependency closure
against Mathlib.

## Reproducing The Checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and enable the nanoda replay.  Each challenge elaborates standalone against
this repository's Mathlib toolchain, e.g.

```bash
bash ORRWAudit/check_standalone.sh ORRWAudit/RangeLowerBound/Challenge.lean
bash ORRWAudit/check_standalone.sh --vocabulary
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'`
warning per challenge; the second command checks that the vocabulary block of
each challenge is byte-identical to that of its `SolutionBasic.lean`.  The
solutions build with

```bash
lake build ORRWAudit
```

Then, with `leanprover/comparator`, `lean4export` (at the toolchain's tag), `landrun` and
`nanoda` built at the pins of [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md), from the repository
root:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator ORRWAudit/<Pair>/comparator.json
```

**Status.**  All four solutions build.  `leanprover/comparator` passes on all four pairs,
with the Lean kernel and again with the independent nanoda kernel.
[`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md) records the pins, the results and
the reproduction steps.  The workflow
[`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml) runs
it on request.
