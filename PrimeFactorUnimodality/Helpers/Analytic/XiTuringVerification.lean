import PrimeFactorUnimodality.Helpers.Analytic.TuringCountingBudget
import PrimeFactorUnimodality.Helpers.Analytic.XiBlockSummary
import PrimeFactorUnimodality.Helpers.Analytic.XiIntegralVerification

/-! # Finite critical-line completeness with a proved Turing budget

Ordered sign rows and one explicit endpoint inequality now suffice for
low-height completeness. The integrated actual-count error is discharged
by the analytic theorem, not left as a supplied hypothesis. Multiplicity
labels and rational endpoint areas retain the existing verifier's meaning.
-/

namespace PrimeFactorUnimodality

noncomputable section

namespace XiSignRows

/-- A sign-row margin against the proved Turing budget certifies every low-height divisor label. -/
theorem Valid.low_criticalLine_of_turing_margin {n : ℕ} {rows : Fin n → XiSignRow}
    {a b : ℚ} (hrows : Valid rows 0 b) (ha : 32 ≤ a) (hab : a ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b < (b : ℝ) - a + (completedAreaRat rows a b : ℝ)) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  have har : (32 : ℝ) ≤ a := by exact_mod_cast ha
  have habr : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact hrows.low_criticalLine_of_remainder_integral (by linarith) hab
    (integral_xiZeroCountingRemainder_le_turingBudget har habr) hmargin

/-- A scalar area summary suffices; the completeness consumer never needs the endpoint vector. -/
theorem AreaSummary.low_criticalLine_of_turing_margin {n : ℕ} {a b area : ℚ}
    (h : AreaSummary n 0 b a b area) (ha : 32 ≤ a) (hab : a ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b < (b : ℝ) - a + area) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  obtain ⟨rows, hr, harea⟩ := h
  apply hr.low_criticalLine_of_turing_margin ha hab
  have harea' : (area : ℝ) ≤ completedAreaRat rows a b := by exact_mod_cast harea
  exact hmargin.trans_le (add_le_add le_rfl harea')

/-- Only the overshoot rows need an area sum; the entire earlier prefix contributes its count. -/
theorem CountSummary.low_criticalLine_of_turing_tail {n m : ℕ} {cut a b area : ℚ}
    (h : CountSummary n 0 cut) (htail : AreaSummary m cut b a b area)
    (hcut : cut ≤ a) (ha : 32 ≤ a) (hab : a ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral a +
      turingCountErrorBudget a b < (b : ℝ) - a + (n : ℝ) * ((b : ℝ) - a) + area) :
    ∀ p ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  apply ((h.area_before hcut).append htail).low_criticalLine_of_turing_margin ha hab
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_sub, add_assoc] using hmargin

end XiSignRows

end

end PrimeFactorUnimodality
