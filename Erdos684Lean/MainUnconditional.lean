import Erdos684Lean.Main
import Erdos684Lean.PNT

/-!
# The unconditional main theorem

`Erdos684.main_theorem` and `Erdos684.unbounded` take the prime number theorem (with a
power-of-logarithm remainder) as the hypothesis `PNTHyp`.  Here that hypothesis is discharged by
`Erdos684.pntHyp`, which is derived from `PrimeNumberTheoremAnd.MediumPNT`, so the results below
have no hypotheses at all.
-/

open Filter Topology Real

namespace Erdos684

/-- Paper Theorem 1.2, (4), unconditionally: for every `ε > 0` there are arbitrarily large `n`
with `f(n) > (1/2 − ε) log n · log log n / log log log n`. -/
theorem main_theorem_unconditional (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, ∀ k : ℕ,
      (k : ℝ) ≤ (1 / 2 - ε) * Real.log n * Real.log (Real.log n) /
          Real.log (Real.log (Real.log n)) →
        (k : ℕ∞) < fThr n :=
  main_theorem pntHyp ε hε

/-- Paper (5), unconditionally: `f(n)/log n` is unbounded. -/
theorem unbounded_unconditional (C : ℝ) :
    ∃ᶠ n : ℕ in atTop, ∀ k : ℕ, (k : ℝ) ≤ C * Real.log n → (k : ℕ∞) < fThr n :=
  unbounded pntHyp C

end Erdos684
