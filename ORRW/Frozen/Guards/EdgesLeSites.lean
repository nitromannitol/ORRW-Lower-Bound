/-
Every subgraph of `ℤ^d` on `m` vertices has at most `d m` edges.

Paper line encoded, `orrw.tex` (equation `eq:edges-sites`):

  "Every subgraph of \$\Z^d\$ on \$m\$ vertices has at most \$dm\$ edges, so
   \$|E_n|\leq d|R_n|\$."

This is the step that converts crossed edges into visited sites in both main
proofs.
-/
import ORRW.Basic
import ORRW.Support.Guards

open ORRW Finset

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.card_edges_le_card_range {d n : ℕ} (w : Fin n → ORRW.Dir d) (k : ℕ) :
    (ORRW.E w k).card ≤ d * (ORRW.R w k).card
-- FROZEN-STATEMENT-END
:= _root_.ORRW.card_edges_le_card_range w k
