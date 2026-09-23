import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.XiIntegralVerification

/-! # Exact interfaces and endpoint regressions for integrated zero verification -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Finset MeasureTheory

open XiSignRows

local instance : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _

example {n : ℕ} {rows : Fin n → XiSignRow}
    {a : ℝ} {b : ℚ} (h : Valid rows 0 b) (hab : a ≤ (b : ℝ))
    (hbudget : (∫ t in a..(b : ℝ), (xiZeroCount t : ℝ)) <
      (b : ℝ) - a + completedArea rows a b) :
    ∀ p ∈ xiLowHeightIndices a, (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  exact PrimeFactorUnimodality.XiSignRows.Valid.low_criticalLine_of_count_integral h hab hbudget

example {n : ℕ} {rows : Fin n → XiSignRow}
    {a E : ℝ} {b : ℚ} (h : Valid rows 0 b) (hab : a ≤ (b : ℝ))
    (F : ℝ → ℝ) (hF : IntervalIntegrable F volume a b)
    (herror : (∫ t in a..(b : ℝ), ((xiZeroCount t : ℝ) - F t)) ≤ E)
    (hmargin : (∫ t in a..(b : ℝ), F t) + E < (b : ℝ) - a + completedArea rows a b) :
    ∀ p ∈ xiLowHeightIndices a, (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  exact PrimeFactorUnimodality.XiSignRows.Valid.low_criticalLine_of_error_integral h hab F hF herror hmargin

example {n : ℕ} {rows : Fin n → XiSignRow}
    {a b : ℚ} {E : ℝ} (h : Valid rows 0 b) (ha : 0 < a) (hab : a ≤ b)
    (herror : (∫ t in (a : ℝ)..(b : ℝ), xiZeroCountingRemainder t) ≤ E)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a + E <
      (b : ℝ) - a + (completedAreaRat rows a b : ℝ)) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  exact PrimeFactorUnimodality.XiSignRows.Valid.low_criticalLine_of_remainder_integral h ha hab herror hmargin


example {n : ℕ} (rows : Fin n → XiSignRow) {a b : ℚ}
    (h : Valid rows 0 b) (hab : (a : ℝ) ≤ b)
    (hbudget : (∫ t in (a : ℝ)..(b : ℝ), (xiZeroCount t : ℝ)) <
      (b : ℝ) - a + (completedAreaRat rows a b : ℝ)) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  rw [cast_completedAreaRat] at hbudget
  exact h.low_criticalLine_of_count_integral hab hbudget

example {n : ℕ} {rows : Fin n → XiSignRow} {a b : ℚ} {E : ℝ}
    (h : Valid rows 0 b) (ha : 0 < a) (hab : a ≤ b)
    (herror : (∫ t in (a : ℝ)..(b : ℝ), xiZeroCountingRemainder t) ≤ E)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a + E <
      (b : ℝ) - a + (completedAreaRat rows a b : ℝ))
    (p : RiemannXiDivisorZeroIndex) (hp : (riemannXiDivisorZeroValue p).im < 0)
    (hpa : -(riemannXiDivisorZeroValue p).im < (a : ℝ)) :
    (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  apply h.low_criticalLine_of_remainder_integral ha hab herror hmargin p
  rw [mem_xiLowHeightIndices, abs_of_neg hp]
  exact hpa

end

end PrimeFactorUnimodality.Tests
