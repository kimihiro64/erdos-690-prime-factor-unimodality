import PrimeFactorUnimodality.Helpers.Analytic.DusartThetaSquaredEndpoint
import PrimeFactorUnimodality.Helpers.Analytic.KadiriR6FourPoints
import PrimeFactorUnimodality.Helpers.Analytic.MossinghoffTrudgianBounds
import PrimeFactorUnimodality.Helpers.Analytic.XiTuringVerification

/-! # Reduced-height finite inputs for the psi endpoint and region bootstrap

The actual psi and middle-band theta bounds target the twenty-five-million
cutoff, with sign rows extending to the endpoint of the Turing counting
margin. The starting constant 69 is proved from the bounded initial region.
The improved region consumes a valid chain or the common four transform
margins; no numerical transform value or finite sign is asserted here.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The reduced sign rows and Turing margin suffice for the actual complete psi ray. -/
theorem abs_psi_sub_div_lt_of_reduced_turing_rows {n : ℕ} {rows : Fin n → XiSignRow}
    {b : ℚ} (hrows : XiSignRows.Valid rows 0 b) (hb : 25000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 25000000 +
      turingCountErrorBudget 25000000 b <
        (b : ℝ) - 25000000 + (XiSignRows.completedAreaRat rows 25000000 b : ℝ))
    {x : ℝ} (hx : (1441000000000 : ℝ) ≤ x) :
    |Chebyshev.psi x - x| / x < (1 / 36260 : ℝ) := by
  have hlow := hrows.low_criticalLine_of_turing_margin (by norm_num) hb hmargin
  exact abs_psi_sub_div_lt_of_reduced_low_gap hx (fun p hp => (hlow p hp).le)

/-- The same reduced verification controls the entire log-square endpoint band. -/
theorem abs_theta_sub_lt_logSquared_of_reduced_turing_rows
    {n : ℕ} {rows : Fin n → XiSignRow} {b : ℚ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 25000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 25000000 +
      turingCountErrorBudget 25000000 b <
        (b : ℝ) - 25000000 + (XiSignRows.completedAreaRat rows 25000000 b : ℝ))
    {x : ℝ} (hx : (1441000000000 : ℝ) ≤ x) (hlog : log x ≤ 85) :
    |Chebyshev.theta x - x| < (1 / 5 : ℝ) * x / log x ^ 2 :=
  abs_theta_sub_lt_logSquared_of_psi_endpoint hx hlog
    (abs_psi_sub_div_lt_of_reduced_turing_rows hrows hb hmargin hx)

/-- A valid reduced-height chain needs no assumed starting region. -/
theorem kadiriHighRegion_of_reduced_turing_rows
    {n : ℕ} {rows : Fin n → XiSignRow} {b : ℚ} {r : ℝ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 25000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 25000000 +
      turingCountErrorBudget 25000000 b <
        (b : ℝ) - 25000000 + (XiSignRows.completedAreaRat rows 25000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 25000000 69 r) :
    KadiriHighRegion r 25000000 := by
  have hlow := hrows.low_criticalLine_of_turing_margin (by norm_num) hb hmargin
  exact hchain.highRegion (fun i hi => mossinghoffTrudgianCoefficient_nonneg
    (Finset.mem_range.mp hi)) (by simp) mossinghoffTrudgianCoefficient_one_pos
    mossinghoffTrudgianPolynomial_nonneg
    (fun p hp => (hlow p ((mem_xiLowHeightIndices _ _).mpr hp)).le)
    kadiriHighRegion_reduced_initial

/-- The common four transform points and the reduced Turing rows give the actual region at six. -/
theorem kadiriHighRegion_six_of_reduced_rows_and_four_points
    {n : ℕ} {rows : Fin n → XiSignRow} {b : ℚ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 25000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 25000000 +
      turingCountErrorBudget 25000000 b <
        (b : ℝ) - 25000000 + (XiSignRows.completedAreaRat rows 25000000 b : ℝ))
    (hg : (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ))
    (hm : -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ))
    (hd : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ))
    (he : exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100)) (hpoints : KadiriSixTransformBounds) :
    KadiriHighRegion 6 25000000 :=
  kadiriHighRegion_of_reduced_turing_rows hrows hb hmargin
    (kadiriSix_reduced_chain_of_four_points hg hm hd he hpoints)

end

end PrimeFactorUnimodality
