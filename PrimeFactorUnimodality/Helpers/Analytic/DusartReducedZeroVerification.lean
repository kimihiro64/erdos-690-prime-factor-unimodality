import PrimeFactorUnimodality.Helpers.Analytic.DusartThetaSquaredEndpoint
import PrimeFactorUnimodality.Helpers.Analytic.KadiriInitialCutoff
import PrimeFactorUnimodality.Helpers.Analytic.MossinghoffTrudgianBounds
import PrimeFactorUnimodality.Helpers.Analytic.XiTuringVerification

/-! # Reduced-height finite inputs for the psi endpoint and region bootstrap

The actual psi and middle-band theta bounds target the twenty-five-million
cutoff, with sign rows extending to the endpoint of the Turing counting
margin. The starting constant 69 is proved from the bounded initial region.
Improving that region still requires a valid endpoint chain; no numerical
row or finite sign is asserted here.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- No low-zero input is required for the initial constant at the reduced cutoff. -/
theorem kadiriHighRegion_reduced_initial : KadiriHighRegion 69 25000000 := by
  apply kadiriHighRegion_of_initial_cutoff (by norm_num) (by norm_num)
  have hlow := dusart_log_outer_reduced_bounds.1
  rw [log_pow]
  norm_num
  linarith [dusart_log_ten_bounds.2]

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

end

end PrimeFactorUnimodality
