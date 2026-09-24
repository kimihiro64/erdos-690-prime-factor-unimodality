import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.DusartTuringVerification

/-! # Exact interfaces and endpoint cases for the proved Turing counting budget -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

example {n : ℕ} {b area : ℚ}
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 3000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hsummary : XiSignRows.AreaSummary n 0 b 1000000000 b area) (hb : 1000000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 +
      turingCountErrorBudget 1000000000 b < (b : ℝ) - 1000000000 + area)
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 3594641 :=
  hasThetaLogSquaredError_of_earlier_band_and_turing_summary finite hsummary hb hmargin hchain

open Complex Set
open MeasureTheory

example {n : ℕ} {rows : Fin n → XiSignRow}
    {b : ℚ} (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 +
      turingCountErrorBudget 1000000000 b <
        (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    KadiriHighRegion 6 1000000000 := by
  exact PrimeFactorUnimodality.xi_zero_gap_six_of_turing_rows hrows hb hmargin hchain

example {n : ℕ}
    {rows : Fin n → XiSignRow} {b : ℚ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 +
      turingCountErrorBudget 1000000000 b <
        (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_above_endpoint_of_turing_rows hrows hb hmargin hchain

example {n : ℕ}
    {rows : Fin n → XiSignRow} {b : ℚ}
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 +
      turingCountErrorBudget 1000000000 b <
        (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_of_lower_band_and_turing_rows finite hrows hb hmargin hchain



end

end PrimeFactorUnimodality.Tests
