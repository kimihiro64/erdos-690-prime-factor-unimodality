import PrimeFactorUnimodality.Helpers.Analytic.DusartFarPsi
import PrimeFactorUnimodality.Helpers.Analytic.DusartThetaSquaredEndpoint

/-! # The exact log-square theta coefficient on the far ray

The actual psi error and prime-power correction imply coefficient one
fifth above exp(5000). This closes the far analytic portion of the direct
Dusart route, conditional on the explicitly stated low and high zero data.
The remaining earlier bands are retained by the final gluing theorem.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The root correction has a square-log allowance on the entire far ray. -/
theorem dusartThetaRootRelativeCorrection_le_far {x : ℝ}
    (hx : 1 < x) (hb : 4704 ≤ Real.log x) :
    dusartThetaRootRelativeCorrection x ≤ (1 / 500 : ℝ) / Real.log x ^ 2 := by
  have hc := dusartThetaRootRelativeCorrection_le_half_exp hx.le
  have hm := dusartFar_low_moment_le hb
  apply (le_div_iff₀ (pow_pos (Real.log_pos hx) 2)).mpr
  have hscaled := mul_le_mul_of_nonneg_left hc (sq_nonneg (Real.log x))
  have hnonneg := mul_nonneg (sq_nonneg (Real.log x)) (exp_pos (-Real.log x / 2)).le
  nlinarith only [hm, hscaled, hnonneg]

/-- The exact theta coefficient accepts verification at any smaller admissible height. -/
theorem abs_theta_sub_le_logSquared_far_of_height_le {x H : ℝ}
    (hx : 1 < x) (hb : 5000 ≤ Real.log x)
    (hH : 20 ≤ H) (hH₁ : H ≤ 1000000000)
    (hgap : ∀ z ∈ xiLowHeightIndices H,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2 := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hp := abs_psi_sub_div_le_far_of_height_le hx hb hH hH₁ hgap hreg
  have ht := abs_theta_sub_div_le_psi_relative_error hxpos hp
  have hc := dusartThetaRootRelativeCorrection_le_far hx (by linarith)
  have hbound : |Chebyshev.theta x - x| / x ≤ (1 / 5 : ℝ) / Real.log x ^ 2 := by
    calc
      _ ≤ (1 / 20 : ℝ) / Real.log x ^ 2 + (1 / 500 : ℝ) / Real.log x ^ 2 :=
        ht.trans (add_le_add le_rfl hc)
      _ = (13 / 250 : ℝ) / Real.log x ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg (Real.log x))
  exact ((div_le_iff₀ hxpos).mp hbound).trans_eq (by ring)

/-- The original pointwise far estimate retains its exact billion-height interface. -/
theorem abs_theta_sub_le_logSquared_far {x : ℝ} (hx : 1 < x) (hb : 5000 ≤ Real.log x)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2 :=
  abs_theta_sub_le_logSquared_far_of_height_le hx hb (by norm_num) le_rfl hgap hreg

/-- Every smaller admissible verification height supplies the whole unbounded far ray. -/
theorem hasThetaLogSquaredError_far_of_height_le {H : ℝ}
    (hH : 20 ≤ H) (hH₁ : H ≤ 1000000000)
    (hgap : ∀ z ∈ xiLowHeightIndices H,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) (exp 5000) := by
  intro x hx
  have hx1 : 1 < x := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 5000)).trans_le hx
  have hb := Real.log_le_log (exp_pos 5000) hx
  rw [log_exp] at hb
  exact abs_theta_sub_le_logSquared_far_of_height_le hx1 hb hH hH₁ hgap hreg

/-- The original far-ray provider is the billion-height specialization. -/
theorem hasThetaLogSquaredError_far
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) (exp 5000) :=
  hasThetaLogSquaredError_far_of_height_le (by norm_num) le_rfl hgap hreg

/-- The remaining log-square estimate is reduced to two bounded bands and the zero inputs. -/
theorem hasThetaLogSquaredError_of_bands_and_zero_data
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (middle : ∀ x : ℝ, exp 85 ≤ x → x ≤ exp 5000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hgap : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ))
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, (1000000000 : ℝ) ≤
      |(riemannXiDivisorZeroValue z).im| → (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  apply hasThetaLogSquaredError_of_endpoint_band_and_tail finite _ hgap
  intro x hx
  by_cases hfar : exp 5000 ≤ x
  · exact hasThetaLogSquaredError_far hgap hreg x hfar
  · exact middle x hx (le_of_not_ge hfar)

end

end PrimeFactorUnimodality
