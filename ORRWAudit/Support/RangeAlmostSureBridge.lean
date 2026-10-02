import Mathlib
import ORRW.MainTheorems
import ORRWAudit.RangeAlmostSure.SolutionBasic

/-!
# Bridge for `RangeAlmostSure`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`ORRWAudit/RangeAlmostSure/SolutionBasic.lean`, a verbatim copy of the
vocabulary block of `ORRWAudit/RangeAlmostSure/Challenge.lean`, namespace `ORRWAudit`) is a
statement-level copy of the repository definitions.  Every declaration is a definition over
Mathlib types, written token for token as in `LatticeProb/Site.lean` and
`LatticeProb/Walk/Basic.lean` of the shared library (`Site`, `Dir`, `dirVec`, `pos`, `edgeAt`,
which `ORRW/Basic.lean` re-exports under the `ORRW` namespace), `ORRW/Basic.lean` and
`ORRW/Support/InfinitePath.lean`.  The lemmas below identify the definitions that the statement
of `RangeAlmostSure` mentions, each with its repository counterpart.  None is recursive, so each
identification is `rfl`, which the kernel checks by unfolding both sides.  The one structure
value, the kernel `kappa`, is built with the same fields on both sides, and its measurability
field is a proof, so `rfl` covers it too; the Markov-kernel instance that `pathMeasure` takes is
a proof of a `Prop`, and so it matters only up to proof irrelevance.  Nothing is asserted.
-/

namespace ORRWAudit.Bridge

theorem Site_eq : @ORRWAudit.Site = @LatticeProb.Site := rfl

theorem Dir_eq : @ORRWAudit.Dir = @LatticeProb.Dir := rfl

theorem dirVec_eq : @ORRWAudit.dirVec = @LatticeProb.dirVec := rfl

theorem pos_eq : @ORRWAudit.pos = @LatticeProb.pos := rfl

theorem edgeAt_eq : @ORRWAudit.edgeAt = @LatticeProb.edgeAt := rfl

theorem E_eq : @ORRWAudit.E = @ORRW.E := rfl

theorem R_eq : @ORRWAudit.R = @ORRW.R := rfl

theorem stepWeight_eq : @ORRWAudit.stepWeight = @ORRW.stepWeight := rfl

theorem totalWeight_eq : @ORRWAudit.totalWeight = @ORRW.totalWeight := rfl

theorem ofPrefix_eq : @ORRWAudit.ofPrefix = @ORRW.ofPrefix := rfl

theorem ofPath_eq : @ORRWAudit.ofPath = @ORRW.ofPath := rfl

theorem stepPMF_eq : @ORRWAudit.stepPMF = @ORRW.stepPMF := rfl

theorem initPMF_eq : @ORRWAudit.initPMF = @ORRW.initPMF := rfl

theorem stepMeasure_eq : @ORRWAudit.stepMeasure = @ORRW.stepMeasure := rfl

theorem initMeasure_eq : @ORRWAudit.initMeasure = @ORRW.initMeasure := rfl

theorem kappa_eq : @ORRWAudit.kappa = @ORRW.kappa := rfl

theorem initTraj_eq : @ORRWAudit.initTraj = @ORRW.initTraj := rfl

theorem pathMeasure_eq : @ORRWAudit.pathMeasure = @ORRW.pathMeasure := rfl

end ORRWAudit.Bridge
