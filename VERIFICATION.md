# Paper and Lean correspondence

This note applies to the manuscript snapshot recorded in
[paper/README.md](paper/README.md). The [result map](README.md#which-lean-theorem-proves-which-result)
links all 16 theorem, lemma, and proposition environments to their Lean
statements. There are 24 frozen declarations, including supporting statements
about the probability law and separate almost-sure conclusions.

The Lean kernel checks the formal statements and their proofs. Matching those
statements to the paper requires mathematical review. Hashes and source-label
checks detect changes; they do not perform that review.

## Constants

The paper now uses `C ≥ 1` and `C⁻¹` where the frozen statements sometimes use
separate `c > 0`, `C > 0`, or `K > 0`. These are dimension-dependent existence
claims. Taking the paper's constant at least `max(1, C, K, 1/c)` gives its upper
and lower bounds. In a tail estimate, increasing the time threshold or decreasing
the range threshold shrinks the event, while replacing `c` by a smaller positive
constant weakens the exponential upper bound. Thus the common-constant convention
does not require changing the frozen statements. A maximum also combines the
constants for expectation and almost-sure bounds in Proposition 6.1.

Lemma 8.1 is different: its explicit gradient constant is part of the statement.
Both paper and Lean give `4 d^(3/2) sqrt(R)` for the sum over undirected edges.
Lean indexes each such edge once by a site and a positive coordinate direction.

## Differences in formulation

- **Finite and infinite paths.** Fixed-time expectations and probabilities use
  finite direction histories. `pathMeasure_restr` identifies these laws with
  the marginals of the infinite-path measure. The almost-sure range and
  displacement theorems use that measure and prove eventual lower bounds,
  which imply the paper's liminf bounds.
- **Exit times.** The displacement theorem bounds every finite partial sum of
  exit-time tail probabilities. Monotone convergence gives the paper's expected
  exit time. This passage is a correspondence argument; the frozen export is
  the finite-horizon statement.
- **Exit-time normalization.** The paper and Lean define `u_A = -Δ_A⁻¹ 1`.
  For the discrete-time simple random walk used in the current paper,
  `2d u_A(x)` is the expected exit time. The older continuous-time description
  in the header of `ORRW/Lattice.lean` uses rate one along each edge, for which
  `u_A` itself is the expected exit time. The algebraic definition is unchanged;
  the probabilistic interpretation is not a separate frozen theorem.
- **Effective resistance.** `ORRW.Reff` is defined by the inverse diagonal of
  the Dirichlet Laplacian. The electrical-network interpretation of this
  quantity is not separately formalized. The algebraic identities and bounds
  of Lemma 2.2 are proved for that definition.
- **Supermartingales.** Lemma 3.1 is expressed as the one-step conditional drift
  inequality on each finite history. Lemma 5.1 uses finite-history processes
  and a clock with predictable increments in `{0,1}`. Stopped adapted processes
  and the clock `n ∧ ζ` satisfy these conditions. The correspondence with the
  paper's stochastic-process formulation is explained in the source headers.
- **Uniformity in a site.** A bound for the supremum over sites is represented
  by a universal quantifier over sites inside the constant's scope.
- **Occupation corollary.** The current `eq:cesaro` bounds the sum of return
  probabilities by `C (1 + (β−1)^(d/(d+1))) n^(1/(d+1))`.
  The frozen `occupation_cesaro` instead bounds their average by
  `C β n^(−d/(d+1))`. It is a weaker consequence, not the literal updated
  display. The dimension-specific interval estimate in `occupation` retains
  the sharper `(β−1)` dependence and implies the updated display by the
  elementary simplification given in the paper. That sharper corollary has
  not been added as a separate Lean declaration.

The manuscript revisions moved the occupation corollaries out of
Theorem 8.2 and changed constant notation. No frozen declaration or proof was
changed in this repository preparation. Source comments and the result map
were updated to describe the revised snapshot.

## Reproducing the checks

Run `python3 tools/verify.py`. The generated [certificate](CERTIFICATE.md)
records the source hash, frozen statement hashes, toolchain, and axiom audit.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. The checker
rejects failed Lean commands, missing exports, and unexpected axioms, including
`sorryAx`.

The manifest's `SEALED` status records a successful check; it does not assert
an independent mathematical audit. The clause, exponent, and constant scans
are review aids, and their recorded exceptions must be read with the statements.
The formalization does not cover the literature survey, simulations, figures,
open questions, or the electrical interpretation noted above.
