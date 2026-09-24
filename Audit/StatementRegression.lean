import Audit.Support.Statements
import Audit.RangeLowerBound.Solution
import Audit.RangeTail.Solution
import Audit.RangeAlmostSure.Solution
import Audit.OccupationMeasure.Solution

/-!
# Statement regression for the comparator solutions

For each audited theorem, checks that the type of the solution theorem is
exactly the proposition elaborated in the challenge environment
(`Audit/Support/Statements.lean`), and that it mentions no constant of the
repository namespace `ORRW` or of the shared library namespace `LatticeProb`.
Building this module prints one line per theorem; any mismatch is an error.
This is a local proxy for the statement-identity part of
`leanprover/comparator`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (thm, stmt) in [
    (`ORRWAudit.range_lower_bound, `ORRWAudit.Statements.range_lower_bound),
    (`ORRWAudit.range_tail, `ORRWAudit.Statements.range_tail),
    (`ORRWAudit.range_ae, `ORRWAudit.Statements.range_ae),
    (`ORRWAudit.occupation_measure, `ORRWAudit.Statements.occupation_measure)] do
    let some ti := env.find? thm | throwError "missing theorem {thm}"
    let some si := env.find? stmt | throwError "missing statement {stmt}"
    let some v := si.value? | throwError "statement {stmt} has no value"
    -- A `def` abstracts the proofs inside its value into auxiliary lemmas
    -- (`ORRWAudit.Statements.*._proof_i`, shared between declarations);
    -- put their proof terms back before comparing.
    let v := v.replace fun e => match e with
      | .const n ls =>
        if (`ORRWAudit.Statements).isPrefixOf n && n.isInternal then
          (env.find? n).bind fun ci => (ci.value? (allowOpaque := true)).map (·.instantiateLevelParams ci.levelParams ls)
        else none
      | _ => none
    let v ← liftCoreM (Core.betaReduce v)
    let ty ← liftCoreM (Core.betaReduce ti.type)
    unless ty == v do
      throwError "{thm}: the solution statement differs from the challenge statement"
    for c in ti.type.getUsedConstants do
      if (`ORRW).isPrefixOf c || (`LatticeProb).isPrefixOf c then
        throwError "{thm} mentions the repository constant {c}"
    logInfo m!"{thm}: identical to the challenge statement; no repository constant"

#print axioms ORRWAudit.range_lower_bound
#print axioms ORRWAudit.range_tail
#print axioms ORRWAudit.range_ae
#print axioms ORRWAudit.occupation_measure
