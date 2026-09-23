import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.XiTuringVerification

/-! # Exact interfaces and endpoint cases for the proved Turing counting budget -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Set
open MeasureTheory
open PrimeFactorUnimodality.XiSignRows

example {n : ℕ} {rows : Fin n → XiSignRow}
    {a b : ℚ} (hrows : Valid rows 0 b) (ha : 32 ≤ a) (hab : a ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b < (b : ℝ) - a + (completedAreaRat rows a b : ℝ)) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  exact PrimeFactorUnimodality.XiSignRows.Valid.low_criticalLine_of_turing_margin hrows ha hab hmargin



end

end PrimeFactorUnimodality.Tests
