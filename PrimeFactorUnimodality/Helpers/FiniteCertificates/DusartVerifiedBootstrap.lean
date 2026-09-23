import PrimeFactorUnimodality.Helpers.Analytic.DusartCheckpointVerification
import PrimeFactorUnimodality.Helpers.Analytic.DusartReducedZeroVerification
import PrimeFactorUnimodality.Helpers.FiniteCertificates.KadiriTransformNumerical

/-! # Dusart consumers with the R6 scalar bootstrap discharged

Only low-height verification and lower-band data remain explicit. The
certified four-point transforms supply the endpoint chain in every consumer.
In particular the full theta ray still requires verification to a billion;
the smaller cutoff is used only for its separate region and psi route.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Actual billion-height low-zero data now suffices for the improved high region. -/
theorem xi_zero_gap_six_of_verified_low
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) : KadiriHighRegion 6 1000000000 :=
  xi_zero_gap_six_of_endpoint_chain kadiriSix_endpoint_chain hlow

/-- The reduced high-region theorem retains its precise smaller low-zero hypothesis. -/
theorem xi_zero_gap_six_of_verified_reduced_low
    (hlow : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) : KadiriHighRegion 6 25000000 :=
  xi_zero_gap_six_of_reduced_endpoint_chain kadiriSix_reduced_endpoint_chain hlow

/-- The complete upper theta ray has no numerical transform or high-region assumption. -/
theorem hasThetaLogSquaredError_above_endpoint_of_verified_low
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 :=
  hasThetaLogSquaredError_above_endpoint_of_bootstrap kadiriSix_endpoint_chain hlow

/-- The exact published theta cutoff retains just lower-band and low-zero obligations. -/
theorem hasThetaLogSquaredError_of_lower_band_and_verified_low
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 :=
  hasThetaLogSquaredError_of_lower_band_and_bootstrap finite kadiriSix_endpoint_chain hlow

/-- Turing signs and the complete counting margin give the entire upper theta ray. -/
theorem hasThetaLogSquaredError_above_endpoint_of_verified_turing_rows {n : ℕ}
    {rows : Fin n → XiSignRow} {b : ℚ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 +
      turingCountErrorBudget 1000000000 b <
        (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 :=
  hasThetaLogSquaredError_above_endpoint_of_turing_rows hrows hb hmargin kadiriSix_endpoint_chain

/-- Checkpoint and Turing data feed the published theta provider with no bootstrap assumption. -/
theorem hasThetaLogSquaredError_of_verified_checkpoints_and_turing_rows
    {p q : ThetaSquaredCheckpoint} {points : List ThetaSquaredCheckpoint}
    (hpoints : ∀ r ∈ points, r.Valid)
    (hsteps : ThetaSquaredCheckpoint.Chain (1 / 5) p q points)
    (hp : p.point ≤ 3594641) (hq : 1441000000000 ≤ q.point)
    {n : ℕ} {rows : Fin n → XiSignRow} {b : ℚ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 +
      turingCountErrorBudget 1000000000 b <
        (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 :=
  hasThetaLogSquaredError_of_checkpoints_and_turing_rows
    hpoints hsteps hp hq hrows hb hmargin kadiriSix_endpoint_chain

end

end PrimeFactorUnimodality
