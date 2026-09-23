import PrimeFactorUnimodality.Helpers.Analytic.DusartEarlierCutoffTheta

/-! # Earlier analytic cutoff interfaces and seam regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real

example {x : ℝ} (hx : (20 : ℝ) ^ 6 ≤ x) :
    dusartThetaRootRelativeCorrection x ≤ 6 * exp (-log x / 2) := by
  exact PrimeFactorUnimodality.dusartThetaRootRelativeCorrection_early_le hx

example {x r : ℝ}
    (hx : (20 : ℝ) ^ 6 ≤ x) (hr : 0 < r) (hrx : r ^ 2 ≤ x) :
    dusartThetaRootRelativeCorrection x ≤ 6 / r := by
  exact PrimeFactorUnimodality.dusartThetaRootRelativeCorrection_early_square_le hx hr hrx

example {x ε B : ℝ}
    (hx : 1 < x) (hB : log x ≤ B) (hε : ε * B ^ 2 ≤ (1 / 5 : ℝ))
    (hθ : |Chebyshev.theta x - x| / x ≤ ε) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  exact PrimeFactorUnimodality.abs_theta_sub_le_logSquared_of_earlier_cap hx hB hε hθ

example {x : ℝ}
    (hx : (10000000000 : ℝ) ≤ x) (hX : x ≤ 100000000000)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  exact PrimeFactorUnimodality.abs_theta_sub_le_logSquared_early_first hx hX hgap

example {x : ℝ}
    (hx : (100000000000 : ℝ) ≤ x) (hX : x ≤ 1441000000000)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  exact PrimeFactorUnimodality.abs_theta_sub_le_logSquared_early_second hx hX hgap

example {x : ℝ}
    (hx : (10000000000 : ℝ) ≤ x) (hX : x ≤ 1441000000000)
    (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2 := by
  exact PrimeFactorUnimodality.abs_theta_sub_le_logSquared_early_bridge hx hX hgap

example (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
    (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta 10000000000 - 10000000000| ≤
      (1 / 5 : ℝ) * 10000000000 / Real.log 10000000000 ^ 2 :=
  abs_theta_sub_le_logSquared_early_first (by norm_num) (by norm_num) hgap

example (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
    (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta 100000000000 - 100000000000| ≤
      (1 / 5 : ℝ) * 100000000000 / Real.log 100000000000 ^ 2 := by
  have first := abs_theta_sub_le_logSquared_early_first
    (x := 100000000000) (by norm_num) (by norm_num) hgap
  have second := abs_theta_sub_le_logSquared_early_second
    (x := 100000000000) (by norm_num) (by norm_num) hgap
  exact first.trans_eq (by rfl)

example (hgap : ∀ z ∈ xiLowHeightIndices 25000000,
    (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta 1441000000000 - 1441000000000| ≤
      (1 / 5 : ℝ) * 1441000000000 / Real.log 1441000000000 ^ 2 :=
  abs_theta_sub_le_logSquared_early_second (by norm_num) (by norm_num) hgap

example : dusartThetaRootRelativeCorrection ((20 : ℝ) ^ 6) ≤
    6 / ((20 : ℝ) ^ 3) :=
  dusartThetaRootRelativeCorrection_early_square_le (by norm_num)
    (by norm_num) (by norm_num)

end

end PrimeFactorUnimodality.Tests
