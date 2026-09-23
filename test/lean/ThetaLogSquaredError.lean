import PrimeFactorUnimodality.Helpers.Analytic.ThetaLogSquaredError

/-! # Regression statements for the direct log-square Dusart route -/

namespace PrimeFactorUnimodality.Tests

example {C X Y : ℝ}
    (error : HasThetaLogSquaredError C X) (hXY : X ≤ Y) :
    HasThetaLogSquaredError C Y :=
  HasThetaLogSquaredError.mono error hXY

end PrimeFactorUnimodality.Tests
