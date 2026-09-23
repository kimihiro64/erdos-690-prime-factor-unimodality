import PrimeFactorUnimodality.Helpers.Analytic.DusartPrimeCountingSquared

/-! # Regression statements for the direct log-square Dusart route -/

namespace PrimeFactorUnimodality.Tests

example {X : ℝ}
    (hX : 2 ≤ X) (hlogX : 10 ≤ Real.log X)
    (error : HasThetaLogSquaredError (1 / 5) X)
    (lowerAnchor : dusartPiLower X ≤ dusartJ 2 (-(1 / 5)) X X)
    (upperAnchor : dusartJ 2 (1 / 5) X X ≤ dusartPiUpper X) :
    HasDusartRealPrimeCountingBoundsAbove X :=
  hasDusartRealPrimeCountingBoundsAbove_of_thetaLogSquared hX hlogX error lowerAnchor upperAnchor

example {X : ℝ}
    (hX : 2 ≤ X) (hlogX : 10 ≤ Real.log X)
    (finite : HasDusartRealPrimeCountingBoundsBelow X)
    (error : HasThetaLogSquaredError (1 / 5) X)
    (lowerAnchor : dusartPiLower X ≤ dusartJ 2 (-(1 / 5)) X X)
    (upperAnchor : dusartJ 2 (1 / 5) X X ≤ dusartPiUpper X) :
    HasDusartPrimeCountingBounds :=
  hasDusartPrimeCountingBounds_of_thetaLogSquared hX hlogX finite error lowerAnchor upperAnchor

end PrimeFactorUnimodality.Tests
