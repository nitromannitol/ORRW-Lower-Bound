/-
Theorem 1.2 of orrw.tex, frozen.

Paper line encoded, `orrw.tex:128-136` (label `thm:whp`):

  "Theorem (Stretched-exponential tail). Let \$d\geq2\$. There are constants
   \$c>0\$ and \$C<\infty\$, depending only on \$d\$, such that for every
   \$\beta\geq1\$ and every integer \$n\$ with \$n/\beta\geq C\$,
   \$\P_\beta\{|R_n|<c\beta^{-d/(d+1)}n^{d/(d+1)}\}
      \leq\exp(-c(n/\beta)^{(d-1)/(d+1)})\$."

The hypothesis `C * β ≤ n` is the paper's `n/β ≥ C` written without division.
-/
import ORRW.Basic
import ORRW.Support.RangeTail

open ORRW

-- FROZEN-STATEMENT-BEGIN
theorem ORRW.Frozen.range_tail (d : ℕ) (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ β : ℝ, 1 ≤ β → ∀ n : ℕ, C * β ≤ (n : ℝ) →
      ORRW.prb (d := d) n β (fun w =>
          ((ORRW.R w n).card : ℝ)
            < c * β ^ (-((d : ℝ) / ((d : ℝ) + 1))) * (n : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)))
        ≤ Real.exp (-(c * ((n : ℝ) / β) ^ (((d : ℝ) - 1) / ((d : ℝ) + 1))))
-- FROZEN-STATEMENT-END
:= ORRW.Support.range_tail_of hd
