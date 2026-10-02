# Comparator design memo: vocabulary, bridges, deltas

This memo records how the four comparator pairs are built, for whoever checks
or extends them.  Each pair `ORRWAudit/<Thm>/` has the same four files, and
each pair has its own bridge under `ORRWAudit/Support/`.

- `Challenge.lean` imports `Mathlib` and nothing else.  It rebuilds from Mathlib
  primitives every object its theorem mentions: the lattice, its direction
  words, the step rule of once-reinforced random walk, its law on words of
  length `n` and on infinite words, with expectation and probability.  It states
  the theorem and ends in a single `sorry`.  This file is the object of trust: a
  reader checks what it says, not how it is proved.
- `SolutionBasic.lean` is a verbatim, mechanical copy of the vocabulary block of
  `Challenge.lean` (between `VOCABULARY-BEGIN` and `VOCABULARY-END`).  It imports
  only `Mathlib`, so the vocabulary elaborates in the solution exactly as in the
  challenge.
- `Solution.lean` imports the repository together with its own `SolutionBasic`
  and its own bridge `ORRWAudit/Support/<Thm>Bridge.lean`, restates the
  challenge theorem byte-for-byte, and proves it from the corresponding theorem
  of `ORRW/MainTheorems.lean`.
- `comparator.json` names the challenge module, the solution module, the theorem
  and the permitted axioms (`propext`, `Classical.choice`, `Quot.sound`), and
  enables the nanoda kernel.

## 0. Solution architecture

The comparator checks that the solution theorem has the same elaborated type
as the challenge theorem, constant by constant through the whole dependency
closure.  So the vocabulary constants must elaborate in the solution exactly
as in the challenge.  The vocabulary is therefore compiled in a module that
imports **only Mathlib** (`<Thm>/SolutionBasic.lean`), and `Solution.lean`
imports the repository, that module, and the pair's bridge, and states the
theorem with the challenge's bytes.

The four challenges share one vocabulary block, byte-identical in each
(`bash ORRWAudit/check_standalone.sh --vocabulary` compares each challenge with
its `SolutionBasic.lean`), so the four `SolutionBasic.lean` files carry the same
block.  The block contains definitions that a given challenge does not use (the
infinite-path measure in all but `RangeAlmostSure`); they do not enter that
theorem's dependency closure.

The Lean namespace of the audit surface is `ORRWAudit` and its modules live
under `ORRWAudit.*`.  The shared library keeps its own audit surface under the
module root `LatticeProbAudit`, so the two never collide in one build.

## 1. The vocabulary has no new structures

Every declaration of the vocabulary is a definition over Mathlib types, a
token-for-token copy of the repository's, or one of two lemmas.  It declares no
structure or inductive type.  The one structure value is the kernel `kappa`,
an element of Mathlib's `ProbabilityTheory.Kernel`.

## 2. Identifications

Each `ORRWAudit/Support/<Thm>Bridge.lean` proves, for every vocabulary
definition that the pair's statement depends on, the equation
`@ORRWAudit.c = @ORRW.c`, or `@ORRWAudit.c = @LatticeProb.c` for those that the
repository takes from the shared library (`Site`, `Dir`, `dirVec`, `pos`,
`edgeAt`).  `RangeAlmostSureBridge.lean` also covers the infinite-path
definitions (`ofPrefix`, `ofPath`, `stepPMF`, `initPMF`, `stepMeasure`,
`initMeasure`, `kappa`, `initTraj`, `pathMeasure`), which only that statement
mentions.  No definition is recursive, so every identification is `rfl`, which
the kernel checks by unfolding both sides.  For `kappa` the measurability field
is a proof, and for `pathMeasure` the Markov-kernel instance is a proof of a
`Prop`, so both are identified up to proof irrelevance.

## 3. Theorem-level bridges

Every constant of each statement is non-recursive, so each solution closes its
goal by `exact` of the theorem of `ORRW/MainTheorems.lean`, the remaining
identifications being definitional.

## 4. Presentation deltas

None at the level of the displayed statements: each challenge theorem is the
statement of the corresponding theorem of `ORRW/MainTheorems.lean` with every
repository name replaced by its vocabulary copy, and each of those is its
frozen statement unchanged.

How each statement reads the paper is recorded in the frozen docstrings and
summarized in [`CORRESPONDENCE.md`](../CORRESPONDENCE.md) and
[`VERIFICATION.md`](../VERIFICATION.md).  The comparator does not check that
reading: it checks that the library proves exactly the displayed statement,
over definitions that can be read without the library.

## 5. What the comparator does not certify

- The faithfulness of the vocabulary to the paper.  The vocabulary is a copy
  of the repository's definitions, so the comparator shows that nothing in the
  statements depends on the library beyond what the vocabulary displays; a
  reader still has to check the vocabulary against the paper.  The model
  guards `ORRW.Frozen.totalWeight_pos`, `ORRW.Frozen.sum_prob_eq_one`,
  `ORRW.Frozen.card_edges_le_card_range` and
  `ORRW.Frozen.expect_card_range_one_step`, and the identification of the
  infinite-path measure with the finite-horizon law
  (`ORRW.Frozen.pathMeasure_restr`), are there to help with that check; they
  are not part of the comparator surface.

## 6. What the comparator checks

The comparator itself checks each solution statement against its challenge,
constant by constant through the whole dependency closure, the closure against
Mathlib, and the axioms of the solution against the permitted three.  Every pair
passes with the Lean kernel and with the independent nanoda kernel; see
[`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md) for the results and the reproduction
steps.  There is no separate local regression: the four solutions cannot be
imported into one module, because each pair has its own copy of the vocabulary.
