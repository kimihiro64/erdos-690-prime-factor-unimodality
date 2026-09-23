import PrimeFactorUnimodality.Helpers.Analytic.DusartZeroVerification

/-! # Exact statement regressions for critical-line verification -/

namespace PrimeFactorUnimodality.Tests

open Complex Finset Set XiSignRows

example {n : ℕ} {rows : Fin n → XiSignRow}
    (hrows : XiSignRows.Valid rows 0 1000000000)
    (hcount : xiStrictZeroCount 1000000000 ≤ n)
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    KadiriHighRegion 6 1000000000 := by
  apply PrimeFactorUnimodality.xi_zero_gap_six_of_sign_rows <;> assumption

example {n : ℕ} {rows : Fin n → XiSignRow}
    (hrows : XiSignRows.Valid rows 0 1000000000)
    (hcount : xiStrictZeroCount 1000000000 ≤ n)
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 := by
  apply PrimeFactorUnimodality.hasThetaLogSquaredError_above_endpoint_of_sign_rows <;> assumption

example {n : ℕ} {rows : Fin n → XiSignRow}
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hrows : XiSignRows.Valid rows 0 1000000000)
    (hcount : xiStrictZeroCount 1000000000 ≤ n)
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  apply PrimeFactorUnimodality.hasThetaLogSquaredError_of_lower_band_and_sign_rows <;> assumption

end PrimeFactorUnimodality.Tests
