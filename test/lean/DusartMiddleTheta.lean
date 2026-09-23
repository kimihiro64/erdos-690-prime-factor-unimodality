import PrimeFactorUnimodality.Helpers.Analytic.DusartMiddleTheta

/-! # Regression statements for the middle-range Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example {x : ℝ}
    (hx : 1 < x) (hb : 84 ≤ Real.log x) :
    dusartThetaRootRelativeCorrection x ≤ (1 / 10000 : ℝ) / Real.log x ^ 2 := by
  apply PrimeFactorUnimodality.dusartThetaRootRelativeCorrection_le_middle <;> assumption

example {x : ℝ}
    (hx : 1 < x) (hb : 85 ≤ Real.log x) (hb₁ : Real.log x ≤ 5000)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2 := by
  apply PrimeFactorUnimodality.abs_theta_sub_le_logSquared_middle <;> assumption

example
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |Chebyshev.theta (exp 85) - exp 85| ≤ (1 / 5 : ℝ) * exp 85 / Real.log (exp 85) ^ 2 :=
  abs_theta_sub_le_logSquared_middle (one_lt_exp_iff.mpr (by norm_num))
    (by rw [log_exp]) (by rw [log_exp]; norm_num) hgap hreg

example
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |Chebyshev.theta (exp 5000) - exp 5000| ≤
      (1 / 5 : ℝ) * exp 5000 / Real.log (exp 5000) ^ 2 :=
  abs_theta_sub_le_logSquared_middle (one_lt_exp_iff.mpr (by norm_num))
    (by rw [log_exp]; norm_num) (by rw [log_exp]) hgap hreg

end PrimeFactorUnimodality.Tests
