import PrimeFactorUnimodality.Helpers.Analytic.DusartReducedZeroVerification

/-! # Height-uniform R6 interfaces, boundaries and actual consumers -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Finset Real

example {n : ℕ} {rows : Fin n → XiSignRow}
    {b : ℚ} (hrows : XiSignRows.Valid rows 0 b) (hb : 25000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 25000000 +
      turingCountErrorBudget 25000000 b <
        (b : ℝ) - 25000000 + (XiSignRows.completedAreaRat rows 25000000 b : ℝ))
    {x : ℝ} (hx : (1441000000000 : ℝ) ≤ x) :
    |Chebyshev.psi x - x| / x < (1 / 36260 : ℝ) := by
  exact PrimeFactorUnimodality.abs_psi_sub_div_lt_of_reduced_turing_rows hrows hb hmargin hx

example
    {n : ℕ} {rows : Fin n → XiSignRow} {b : ℚ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 25000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 25000000 +
      turingCountErrorBudget 25000000 b <
        (b : ℝ) - 25000000 + (XiSignRows.completedAreaRat rows 25000000 b : ℝ))
    {x : ℝ} (hx : (1441000000000 : ℝ) ≤ x) (hlog : log x ≤ 85) :
    |Chebyshev.theta x - x| < (1 / 5 : ℝ) * x / log x ^ 2 := by
  exact PrimeFactorUnimodality.abs_theta_sub_lt_logSquared_of_reduced_turing_rows hrows hb hmargin hx hlog

example
    {n : ℕ} {rows : Fin n → XiSignRow} {b : ℚ} {r : ℝ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 25000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 25000000 +
      turingCountErrorBudget 25000000 b <
        (b : ℝ) - 25000000 + (XiSignRows.completedAreaRat rows 25000000 b : ℝ))
    (hchain : KadiriEndpointChain 16 mossinghoffTrudgianCoefficient 25000000 69 r) :
    KadiriHighRegion r 25000000 := by
  exact PrimeFactorUnimodality.kadiriHighRegion_of_reduced_turing_rows hrows hb hmargin hchain

example
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
    KadiriHighRegion 6 25000000 := by
  exact PrimeFactorUnimodality.kadiriHighRegion_six_of_reduced_rows_and_four_points hrows hb hmargin hg hm hd he hpoints



end

end PrimeFactorUnimodality.Tests
