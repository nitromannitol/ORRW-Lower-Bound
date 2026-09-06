/-
Theorem 1.1 of orrw.tex, frozen.

Paper line encoded, `orrw.tex:106-113` (label `thm:main`, equation `eq:main-range`):

  "Theorem (Range lower bound). Let \$d\geq2\$. There is a constant \$c>0\$,
   depending only on \$d\$, such that for every \$\beta\geq1\$,
   \$\E_\beta|R_n|\geq c\beta^{-d/(d+1)}n^{d/(d+1)}\$ for every integer \$n\geq0\$."

That `c` depends only on `d` is expressed by binding it before `β` and `n`.
-/
import ORRW.Basic
import ORRW.Support.RangeLower

open ORRW

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.range_lower_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ,
      c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1))
        ≤ ORRW.expect (d := d) n β (fun w => ((ORRW.R w n).card : ℝ))
-- FROZEN-STATEMENT-END
:= ORRW.Support.range_lower_bound_of hd
