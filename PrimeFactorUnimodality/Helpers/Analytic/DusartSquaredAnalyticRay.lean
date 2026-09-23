import PrimeFactorUnimodality.Helpers.Analytic.DusartFarTheta
import PrimeFactorUnimodality.Helpers.Analytic.DusartMiddleTheta

/-! # The complete analytic ray for the direct log-square Dusart route

Join the endpoint, middle and far estimates with both common boundaries
included. The only remaining analytic inputs on this ray are the explicit
finite low-zero condition and numerical high-zero region. The lower
bounded band stays separate in the global provider assembler.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The middle and far estimates together supply the full ray beyond exp(85). -/
theorem hasThetaLogSquaredError_above_exp85
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) (exp 85) := by
  intro x hx
  have hx1 : 1 < x := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 85)).trans_le hx
  have hb := Real.log_le_log (exp_pos 85) hx
  rw [log_exp] at hb
  by_cases hfar : 5000 ≤ Real.log x
  · exact abs_theta_sub_le_logSquared_far hx1 hfar hgap hreg
  · exact abs_theta_sub_le_logSquared_middle hx1 hb (le_of_not_ge hfar) hgap hreg

/-- The earlier endpoint band completes the analytic ray above 1441000000000. -/
theorem hasThetaLogSquaredError_above_endpoint
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 := by
  intro x hx
  by_cases hb : Real.log x ≤ 85
  · exact (abs_theta_sub_lt_logSquared_of_endpoint_band hx hb hgap).le
  · apply hasThetaLogSquaredError_above_exp85 hgap hreg x
    exact (exp_le_exp.mpr (le_of_not_ge hb)).trans_eq (exp_log (by linarith : 0 < x))

/-- The full requested coefficient now needs only the lower band and the two zero inputs. -/
theorem hasThetaLogSquaredError_of_lower_band_and_zero_data
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) 3594641 :=
  hasThetaLogSquaredError_of_endpoint_band_and_tail finite
    (hasThetaLogSquaredError_above_exp85 hgap hreg) hgap

end

end PrimeFactorUnimodality
