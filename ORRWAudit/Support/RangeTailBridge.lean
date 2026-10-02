import Mathlib
import ORRW.MainTheorems
import ORRWAudit.RangeTail.SolutionBasic

/-!
# Bridge for `RangeTail`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`ORRWAudit/RangeTail/SolutionBasic.lean`, a verbatim copy of the
vocabulary block of `ORRWAudit/RangeTail/Challenge.lean`, namespace `ORRWAudit`) is a
statement-level copy of the repository definitions.  Every declaration is a definition over
Mathlib types, written token for token as in `LatticeProb/Site.lean` and
`LatticeProb/Walk/Basic.lean` of the shared library (`Site`, `Dir`, `dirVec`, `pos`, `edgeAt`,
which `ORRW/Basic.lean` re-exports under the `ORRW` namespace) and `ORRW/Basic.lean`.  The
lemmas below identify the definitions that the statement of `RangeTail` mentions, each with its
repository counterpart.  None is recursive, so each identification is `rfl`, which the kernel
checks by unfolding both sides.  Nothing is asserted.
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

theorem stepProb_eq : @ORRWAudit.stepProb = @ORRW.stepProb := rfl

theorem prob_eq : @ORRWAudit.prob = @ORRW.prob := rfl

theorem prb_eq : @ORRWAudit.prb = @ORRW.prb := rfl

end ORRWAudit.Bridge
