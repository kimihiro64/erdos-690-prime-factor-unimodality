import PrimeFactorUnimodality.Helpers.Analytic.DusartSquaredBootstrap
import PrimeFactorUnimodality.Helpers.Analytic.XiIntegralVerification

/-! # Actual Dusart consumers of finite critical-line verification

Ordered critical-line sign witnesses and a matching total multiplicity
count supply the low-zero hypothesis of the existing bootstrap and theta
theorems. Alternatively, an integrated counting-discrepancy bound and a
rational endpoint margin supply completeness. Numerical signs, count or
integral bounds, the bootstrap chain and lower theta band remain inputs.
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

/-- An integral budget replaces the exact total-count certificate in the actual region theorem. -/
theorem xi_zero_gap_six_of_integral_rows {n : ℕ} {rows : Fin n → XiSignRow}
    {b : ℚ} {E : ℝ} (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (herror : (∫ t in (1000000000 : ℝ)..(b : ℝ), xiZeroCountingRemainder t) ≤ E)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 + E <
      (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    KadiriHighRegion 6 1000000000 := by
  have hlow := hrows.low_criticalLine_of_remainder_integral (by norm_num) hb herror hmargin
  exact xi_zero_gap_six_of_endpoint_chain hchain (fun p hp => (hlow p hp).le)

/-- The integral verifier feeds the theta estimate on the entire analytic ray. -/
theorem hasThetaLogSquaredError_above_endpoint_of_integral_rows {n : ℕ}
    {rows : Fin n → XiSignRow} {b : ℚ} {E : ℝ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (herror : (∫ t in (1000000000 : ℝ)..(b : ℝ), xiZeroCountingRemainder t) ≤ E)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 + E <
      (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 := by
  have hlow := hrows.low_criticalLine_of_remainder_integral (by norm_num) hb herror hmargin
  exact hasThetaLogSquaredError_above_endpoint_of_bootstrap hchain (fun p hp => (hlow p hp).le)

/-- The same integral verification gives the published cutoff once the lower band is proved. -/
theorem hasThetaLogSquaredError_of_lower_band_and_integral_rows {n : ℕ}
    {rows : Fin n → XiSignRow} {b : ℚ} {E : ℝ}
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (herror : (∫ t in (1000000000 : ℝ)..(b : ℝ), xiZeroCountingRemainder t) ≤ E)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 + E <
      (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  have hlow := hrows.low_criticalLine_of_remainder_integral (by norm_num) hb herror hmargin
  exact hasThetaLogSquaredError_of_lower_band_and_bootstrap finite hchain
    (fun p hp => (hlow p hp).le)

end

end PrimeFactorUnimodality
