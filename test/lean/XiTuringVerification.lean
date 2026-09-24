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

example {n : ℕ} {a b area : ℚ} (h : AreaSummary n 0 b a b area)
    (ha : 32 ≤ a) (hab : a ≤ b)
    (hm : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b < (b : ℝ) - a + area) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 :=
  h.low_criticalLine_of_turing_margin ha hab hm

example {n m : ℕ} {cut a b area : ℚ} (h : CountSummary n 0 cut)
    (htail : AreaSummary m cut b a b area) (hcut : cut ≤ a) (ha : 32 ≤ a) (hab : a ≤ b)
    (hm : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b < (b : ℝ) - a + (n : ℝ) * ((b : ℝ) - a) + area) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 :=
  h.low_criticalLine_of_turing_tail htail hcut ha hab hm

end

end PrimeFactorUnimodality.Tests
