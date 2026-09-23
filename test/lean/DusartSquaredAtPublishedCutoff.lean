import PrimeFactorUnimodality.Helpers.Analytic.DusartSquaredAtPublishedCutoff

/-! # Regression statements for the direct log-square Dusart route -/

namespace PrimeFactorUnimodality.Tests

example :
    (10 : ℝ) ≤ Real.log 3594641 :=
  dusart_log_squared_cutoff_ge_ten

example
    (finite : HasDusartShortIntervalPrimeBelow 3594641)
    (error : HasThetaLogSquaredError (1 / 5) 3594641) : HasDusartShortIntervalPrime :=
  hasDusartShortIntervalPrime_of_published_logSquared finite error

example
    (finite : HasDusartRealPrimeCountingBoundsBelow 3594641)
    (error : HasThetaLogSquaredError (1 / 5) 3594641)
    (lowerAnchor : Chebyshev.theta 3594641 * Real.log 3594641 ^ 2 +
      3594641 * Real.log 3594641 + (1 / 5 : ℝ) * 3594641 ≤
        (Nat.primeCounting 3594641 : ℝ) * Real.log 3594641 ^ 3)
    (upperAnchor : (Nat.primeCounting 3594641 : ℝ) * Real.log 3594641 ^ 3 ≤
      Chebyshev.theta 3594641 * Real.log 3594641 ^ 2 +
        (6381 / 5000 : ℝ) * 3594641 * Real.log 3594641 - (1 / 5 : ℝ) * 3594641) :
    HasDusartPrimeCountingBounds :=
  hasDusartPrimeCountingBounds_of_published_logSquared finite error lowerAnchor upperAnchor

end PrimeFactorUnimodality.Tests
