import PrimeFactorUnimodality.Helpers.Analytic.DusartLogarithmicTheta
import PrimeFactorUnimodality.Helpers.Analytic.ThetaLogSquaredError

/-! # A proved middle range for the published log-square theta error

The already evaluated psi endpoint and root correction prove coefficient
one fifth from 1441000000000 through exp(85). Only the same finite low-zero
condition is used; no additional numerical scalar bound is assumed.
The surrounding prefix and far ray remain separate analytic obligations.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The existing endpoint controls the stronger log-square theta error on this whole band. -/
theorem abs_theta_sub_lt_logSquared_of_endpoint_band {x : ℝ}
    (hx : (1441000000000 : ℝ) ≤ x) (hlog : Real.log x ≤ 85)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    |Chebyshev.theta x - x| < (1 / 5 : ℝ) * x / Real.log x ^ 2 := by
  have hxpos : 0 < x := by linarith
  have hlpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hp := abs_psi_sub_div_lt_of_billion_low_gap hx hgap
  have ht := abs_theta_sub_div_le_psi_relative_error hxpos (le_refl (|Chebyshev.psi x - x| / x))
  have hn : |Chebyshev.theta x - x| / x < (1 / 5 : ℝ) / Real.log x ^ 2 := by
    by_cases hsmall : Real.log x ≤ 64
    · have hc := dusartThetaRootRelativeCorrection_endpoint_le hx
      have hsquare := pow_le_pow_left₀ hlpos.le hsmall 2
      calc
        _ ≤ |Chebyshev.psi x - x| / x + dusartThetaRootRelativeCorrection x := ht
        _ < (1 / 36260 : ℝ) + 3 / 200000 := add_lt_add_of_lt_of_le hp hc
        _ < (1 / 5 : ℝ) / 64 ^ 2 := by norm_num
        _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (pow_pos hlpos 2) hsquare
    · have hheight : Real.log (1000000000 : ℝ) ≤ 21 := by
        rw [show (1000000000 : ℝ) = 10 ^ 9 by norm_num, Real.log_pow]
        norm_num
        linarith [dusart_log_ten_bounds.2]
      have he : Real.exp (-Real.log x / 2) ≤ (1 / 1000000000 : ℝ) := by
        calc
          _ ≤ Real.exp (-Real.log (1000000000 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
          _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      have hc := (dusartThetaRootRelativeCorrection_le_half_exp (by linarith : 1 ≤ x)).trans
        (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 18))
      have hsquare := pow_le_pow_left₀ hlpos.le hlog 2
      calc
        _ ≤ |Chebyshev.psi x - x| / x + dusartThetaRootRelativeCorrection x := ht
        _ < (1 / 36260 : ℝ) + 18 * (1 / 1000000000) := add_lt_add_of_lt_of_le hp hc
        _ < (1 / 5 : ℝ) / 85 ^ 2 := by norm_num
        _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (pow_pos hlpos 2) hsquare
  exact ((div_lt_iff₀ hxpos).mp hn).trans_eq (by ring)

/-- The middle band need not be included in the remaining verification of the full estimate. -/
theorem hasThetaLogSquaredError_of_endpoint_band_and_tail
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (tail : HasThetaLogSquaredError (1 / 5) (Real.exp 85))
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  intro x hx
  by_cases hlo : x ≤ 1441000000000
  · exact finite x hx hlo
  · by_cases hhi : Real.log x ≤ 85
    · exact (abs_theta_sub_lt_logSquared_of_endpoint_band (le_of_not_ge hlo) hhi hgap).le
    · apply tail x
      exact (Real.exp_le_exp.mpr (le_of_not_ge hhi)).trans_eq
        (Real.exp_log (by linarith : 0 < x))

end

end PrimeFactorUnimodality
