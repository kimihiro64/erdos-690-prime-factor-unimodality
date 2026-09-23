import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.DusartZeroVerification

/-! # Exact interfaces and endpoint regressions for integrated zero verification -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Finset MeasureTheory

open XiSignRows

local instance : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _

example {n : ℕ} {rows : Fin n → XiSignRow}
    {b : ℚ} {E : ℝ} (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (herror : (∫ t in (1000000000 : ℝ)..(b : ℝ), xiZeroCountingRemainder t) ≤ E)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 + E <
      (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    KadiriHighRegion 6 1000000000 := by
  exact PrimeFactorUnimodality.xi_zero_gap_six_of_integral_rows hrows hb herror hmargin hchain

example {n : ℕ}
    {rows : Fin n → XiSignRow} {b : ℚ} {E : ℝ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (herror : (∫ t in (1000000000 : ℝ)..(b : ℝ), xiZeroCountingRemainder t) ≤ E)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 + E <
      (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_above_endpoint_of_integral_rows hrows hb herror hmargin hchain

example {n : ℕ}
    {rows : Fin n → XiSignRow} {b : ℚ} {E : ℝ}
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (herror : (∫ t in (1000000000 : ℝ)..(b : ℝ), xiZeroCountingRemainder t) ≤ E)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 + E <
      (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_of_lower_band_and_integral_rows finite hrows hb herror hmargin hchain


end

end PrimeFactorUnimodality.Tests
