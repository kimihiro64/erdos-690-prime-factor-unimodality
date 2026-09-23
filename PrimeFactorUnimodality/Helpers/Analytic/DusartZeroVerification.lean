import PrimeFactorUnimodality.Helpers.Analytic.DusartSquaredBootstrap
import PrimeFactorUnimodality.Helpers.Analytic.XiZeroExhaustion

/-! # Actual Dusart consumers of finite critical-line verification

Ordered critical-line sign witnesses and a matching total multiplicity
count supply the low-zero hypothesis of the existing bootstrap and theta
theorems. The numerical signs, count upper bound, endpoint bootstrap chain
and lower theta band must still be proved; none is asserted here.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Finite sign/count verification supplies exactly the bootstrap's low-height input. -/
theorem xi_zero_gap_six_of_sign_rows {n : ℕ} {rows : Fin n → XiSignRow}
    (hrows : XiSignRows.Valid rows 0 1000000000)
    (hcount : xiStrictZeroCount 1000000000 ≤ n)
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    KadiriHighRegion 6 1000000000 := by
  apply xi_zero_gap_six_of_endpoint_chain hchain
  intro p hp
  exact (hrows.low_criticalLine (by norm_num) (by norm_num) hcount p hp).le

/-- Verified signs and a saturating count imply the theta bound on the complete analytic ray. -/
theorem hasThetaLogSquaredError_above_endpoint_of_sign_rows {n : ℕ} {rows : Fin n → XiSignRow}
    (hrows : XiSignRows.Valid rows 0 1000000000)
    (hcount : xiStrictZeroCount 1000000000 ≤ n)
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 := by
  apply hasThetaLogSquaredError_above_endpoint_of_bootstrap hchain
  intro p hp
  exact (hrows.low_criticalLine (by norm_num) (by norm_num) hcount p hp).le

/-- The same finite verification supplies the theorem at Dusart's published cutoff. -/
theorem hasThetaLogSquaredError_of_lower_band_and_sign_rows {n : ℕ} {rows : Fin n → XiSignRow}
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hrows : XiSignRows.Valid rows 0 1000000000)
    (hcount : xiStrictZeroCount 1000000000 ≤ n)
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  apply hasThetaLogSquaredError_of_lower_band_and_bootstrap finite hchain
  intro p hp
  exact (hrows.low_criticalLine (by norm_num) (by norm_num) hcount p hp).le

end

end PrimeFactorUnimodality
