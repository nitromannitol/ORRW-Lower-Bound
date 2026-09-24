/-
The lazy random walk objects of Bou-Rabee--Peres, Section 8, `orrw.tex`, are
those of the library module `LatticeProb.Walk.Lazy`: the lazy step operator `Q`,
the point mass `delta0` at the origin, and the truncated Green function `gR`.
The frozen statement `ORRW/Frozen/Occupation/LazyGreen.lean` names them with
the `ORRW` prefix, so they are re-exported here under the `ORRW` namespace.
The modelling conventions W-001 to W-003 are recorded in the library module.
-/
import LatticeProb.Walk.Lazy
import ORRW.Basic

namespace ORRW

export LatticeProb (Q delta0 gR)

end ORRW
