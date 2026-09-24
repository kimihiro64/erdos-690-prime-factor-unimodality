import PrimeFactorUnimodality.Helpers.Analytic.DusartEarlierCutoff
import PrimeFactorUnimodality.Helpers.Analytic.DusartZeroVerification
import PrimeFactorUnimodality.Helpers.Analytic.XiTuringVerification

/-! # Actual Dusart consumers of the unconditional Turing count bound

The analytic counting error is proved. These consumers retain only the
finite sign rows, an explicit scalar endpoint margin, the region bootstrap
and, for the lowest cutoff, the lower theta band. No assumed total zero
count or assumed counting-error integral remains.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Scalar zero summaries and the shorter finite theta band give the published coefficient. -/
theorem hasThetaLogSquaredError_of_earlier_band_and_turing_summary {n : ℕ} {b area : ℚ}
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 3000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hsummary : XiSignRows.AreaSummary n 0 b 1000000000 b area) (hb : 1000000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 +
      turingCountErrorBudget 1000000000 b < (b : ℝ) - 1000000000 + area)
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  have hlow := hsummary.low_criticalLine_of_turing_margin (by norm_num) hb hmargin
  have hgap := fun p hp => (hlow p hp).le
  apply hasThetaLogSquaredError_of_earlier_band_and_zero_data finite hgap
  intro p hp
  linarith [xi_zero_gap_six_of_endpoint_chain hchain hgap p hp]

/-- Finite signs and the explicit Turing margin provide the region bootstrap's low-zero input. -/
theorem xi_zero_gap_six_of_turing_rows {n : ℕ} {rows : Fin n → XiSignRow}
    {b : ℚ} (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 +
      turingCountErrorBudget 1000000000 b <
        (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    KadiriHighRegion 6 1000000000 := by
  have hlow := hrows.low_criticalLine_of_turing_margin (by norm_num) hb hmargin
  exact xi_zero_gap_six_of_endpoint_chain hchain (fun p hp => (hlow p hp).le)

/-- The entire upper analytic ray needs no further analytic counting-error hypothesis. -/
theorem hasThetaLogSquaredError_above_endpoint_of_turing_rows {n : ℕ}
    {rows : Fin n → XiSignRow} {b : ℚ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 +
      turingCountErrorBudget 1000000000 b <
        (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 := by
  have hlow := hrows.low_criticalLine_of_turing_margin (by norm_num) hb hmargin
  exact hasThetaLogSquaredError_above_endpoint_of_bootstrap hchain (fun p hp => (hlow p hp).le)

/-- At the published cutoff the lower theta band is retained, but the counting error is discharged. -/
theorem hasThetaLogSquaredError_of_lower_band_and_turing_rows {n : ℕ}
    {rows : Fin n → XiSignRow} {b : ℚ}
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 +
      turingCountErrorBudget 1000000000 b <
        (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 1000000000 56 6) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  have hlow := hrows.low_criticalLine_of_turing_margin (by norm_num) hb hmargin
  exact hasThetaLogSquaredError_of_lower_band_and_bootstrap finite hchain
    (fun p hp => (hlow p hp).le)

end

end PrimeFactorUnimodality
