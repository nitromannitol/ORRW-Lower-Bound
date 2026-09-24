import ORRW.MainTheorems

/-!
# Axioms audit

Building this module prints the axiom dependencies of the four main theorems
of `ORRW/MainTheorems.lean`.  Each must report exactly the three standard
foundational axioms of Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

Nothing is assumed in this development: no theorem takes a cited result as a
hypothesis, and no `axiom` is declared.  `ORRW/Certificate.lean` prints the
axioms of all 24 registered statements.

This file is not imported by the library root; the report runs when it is built
explicitly (`lake build ORRW.Meta.AxiomsAudit`), as continuous integration
does on every push.
-/

#print axioms ORRW.range_lower_bound
#print axioms ORRW.range_tail
#print axioms ORRW.range_ae
#print axioms ORRW.occupation_measure
