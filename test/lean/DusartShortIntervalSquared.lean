import PrimeFactorUnimodality.Helpers.Analytic.DusartShortIntervalSquared

/-! # Regression statements for the direct log-square Dusart route -/

namespace PrimeFactorUnimodality.Tests

example {X x : ℝ}
    (error : HasThetaLogSquaredError (1 / 5) X)
    (hx : X ≤ x) (hx1 : 1 < x) (hlog : 2 ≤ Real.log x) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧
      (q : ℝ) ≤ x * (1 + 1 / (2 * Real.log x ^ 2)) :=
  dusartPrimeInInterval_of_thetaLogSquared error hx hx1 hlog

example {X : ℝ}
    (hX : 1 < X) (hlogX : 2 ≤ Real.log X)
    (finite : HasDusartShortIntervalPrimeBelow X)
    (error : HasThetaLogSquaredError (1 / 5) X) : HasDusartShortIntervalPrime :=
  hasDusartShortIntervalPrime_of_thetaLogSquared hX hlogX finite error

example {X : ℝ} (error : HasThetaLogSquaredError (1 / 5) X)
    (hX : 1 < X) (hlogX : 2 ≤ Real.log X) :
    ∃ q : ℕ, q.Prime ∧ X < q ∧
      (q : ℝ) ≤ X * (1 + 1 / (2 * Real.log X ^ 2)) :=
  dusartPrimeInInterval_of_thetaLogSquared error le_rfl hX hlogX

end PrimeFactorUnimodality.Tests
