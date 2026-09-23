import PrimeFactorUnimodality.Helpers.Analytic.DusartLogarithmicTheta
import PrimeFactorUnimodality.Helpers.Analytic.DusartMiddlePsi

/-! # The exact log-square theta coefficient throughout the middle band

The actual pointwise psi estimate leaves room for the prime-power
correction. Thus every real base with logarithm between 85 and 5000
satisfies coefficient one fifth, with only the stated zero-location inputs.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The root correction has a small square-log moment from logarithmic height 84 onwards. -/
theorem dusartThetaRootRelativeCorrection_le_middle {x : ℝ}
    (hx : 1 < x) (hb : 84 ≤ Real.log x) :
    dusartThetaRootRelativeCorrection x ≤ (1 / 10000 : ℝ) / Real.log x ^ 2 := by
  have hc := dusartThetaRootRelativeCorrection_le_half_exp hx.le
  have hm := dusartMiddle_low_moment_le hb
  apply (le_div_iff₀ (pow_pos (Real.log_pos hx) 2)).mpr
  have hscaled := mul_le_mul_of_nonneg_left hc (sq_nonneg (Real.log x))
  have hnonneg := mul_nonneg (sq_nonneg (Real.log x)) (exp_pos (-Real.log x / 2)).le
  nlinarith only [hm, hscaled, hnonneg]

/-- The actual theta error satisfies the requested coefficient at every middle-range point. -/
theorem abs_theta_sub_le_logSquared_middle {x : ℝ}
    (hx : 1 < x) (hb : 85 ≤ Real.log x) (hb₁ : Real.log x ≤ 5000)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2 := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hp := abs_psi_sub_div_le_middle hx hb hb₁ hgap hreg
  have ht := abs_theta_sub_div_le_psi_relative_error hxpos hp
  have hc := dusartThetaRootRelativeCorrection_le_middle hx (by linarith)
  have hbound : |Chebyshev.theta x - x| / x ≤ (1 / 5 : ℝ) / Real.log x ^ 2 := by
    calc
      _ ≤ (19 / 100 : ℝ) / Real.log x ^ 2 + (1 / 10000 : ℝ) / Real.log x ^ 2 :=
        ht.trans (add_le_add le_rfl hc)
      _ = (1901 / 10000 : ℝ) / Real.log x ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg (Real.log x))
  exact ((div_le_iff₀ hxpos).mp hbound).trans_eq (by ring)

end

end PrimeFactorUnimodality
