import PrimeFactorUnimodality.Helpers.Analytic.PlattContourIntegrand
import PrimeFactorUnimodality.Helpers.Analytic.PlattNegativeGammaIntegral

set_option autoImplicit false

/-! # Bounds on the displaced Fourier integrals

The full complex integrand is controlled on the lines corresponding to
Gamma real parts `+(m+1/2)` and `-(m+1/2)`. Both integrals converge and their
bounds retain the exact Gaussian shift cost and Fourier frequency factor.
The contour deformation and the residues crossed in the negative direction
are separate obligations; no equality with the original transform is assumed.
-/

open MeasureTheory

namespace PrimeFactorUnimodality

/-- The downward shift has a polynomial factor bounded by the positive scalar window. -/
theorem norm_plattContourIntegrand_right_le (m k : ℕ) (t₀ h u v : ℝ) :
    ‖plattContourIntegrand k t₀ h u
      ((v : ℂ) + ((-(2 * (m : ℝ) + 1 / 2) : ℝ) : ℂ) * Complex.I)‖ ≤
      ((2 * Real.pi) ^ k *
        Real.exp ((2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) -
          2 * Real.pi * u * (2 * (m : ℝ) + 1 / 2))) * plattGammaWindow m k t₀ h v := by
  have hg : ((1 / 4 - -(2 * (m : ℝ) + 1 / 2) / 2 : ℝ) : ℂ) =
      ((2 * (m : ℝ) + 1 : ℝ) : ℂ) / 2 := by push_cast; ring
  have he : (-(2 * (m : ℝ) + 1 / 2)) ^ 2 / (2 * h ^ 2) +
      2 * Real.pi * u * -(2 * (m : ℝ) + 1 / 2) =
        (2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) -
          2 * Real.pi * u * (2 * (m : ℝ) + 1 / 2) := by ring
  have hp : ‖((-(2 * (m : ℝ) + 1 / 2) : ℝ) : ℂ) - (v : ℂ) * Complex.I‖ ≤
      ‖((2 * (m : ℝ) + 3 / 2 : ℝ) : ℂ) - (v : ℂ) * Complex.I‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    norm_num [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  rw [norm_plattContourIntegrand_on_line, hg, he]
  unfold plattGammaWindow
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hp k) (by positivity))
    (by positivity)

/-- The upward shift has exactly the negative scalar window, not an uncorrected positive one. -/
theorem norm_plattContourIntegrand_left (m k : ℕ) (t₀ h u v : ℝ) :
    ‖plattContourIntegrand k t₀ h u
      ((v : ℂ) + ((2 * (m : ℝ) + 3 / 2 : ℝ) : ℂ) * Complex.I)‖ =
      ((2 * Real.pi) ^ k *
        Real.exp ((2 * (m : ℝ) + 3 / 2) ^ 2 / (2 * h ^ 2) +
          2 * Real.pi * u * (2 * (m : ℝ) + 3 / 2))) *
            plattNegativeGammaWindow m k t₀ h v := by
  rw [norm_plattContourIntegrand_on_line]
  have hg : ((1 / 4 - (2 * (m : ℝ) + 3 / 2) / 2 : ℝ) : ℂ) =
      -(((m : ℝ) + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hg]
  rfl

/-- Absolute convergence on every rightward Gamma shift used by the error estimate. -/
theorem integrable_plattContourIntegrand_right (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    Integrable (fun v : ℝ => plattContourIntegrand k t₀ h u
      ((v : ℂ) + ((-(2 * (m : ℝ) + 1 / 2) : ℝ) : ℂ) * Complex.I)) := by
  apply ((integrable_plattGammaWindow m k hm ht₀ hh).const_mul
    ((2 * Real.pi) ^ k * Real.exp ((2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) -
      2 * Real.pi * u * (2 * (m : ℝ) + 1 / 2)))).mono'
    (((measurable_plattContourIntegrand k t₀ h u).comp (by fun_prop)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (norm_plattContourIntegrand_right_le m k t₀ h u)

/-- Absolute convergence on the leftward Gamma shift, after retaining its correction factor. -/
theorem integrable_plattContourIntegrand_left (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    Integrable (fun v : ℝ => plattContourIntegrand k t₀ h u
      ((v : ℂ) + ((2 * (m : ℝ) + 3 / 2 : ℝ) : ℂ) * Complex.I)) := by
  apply ((integrable_plattNegativeGammaWindow m k hm ht₀ hh).const_mul
    ((2 * Real.pi) ^ k * Real.exp ((2 * (m : ℝ) + 3 / 2) ^ 2 / (2 * h ^ 2) +
      2 * Real.pi * u * (2 * (m : ℝ) + 3 / 2)))).mono'
    (((measurable_plattContourIntegrand k t₀ h u).comp (by fun_prop)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun v => (norm_plattContourIntegrand_left m k t₀ h u v).le)

/-- Bound for the actual displaced integral in the positive-frequency direction. -/
theorem norm_integral_plattContourIntegrand_right_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    ‖∫ v : ℝ, plattContourIntegrand k t₀ h u
      ((v : ℂ) + ((-(2 * (m : ℝ) + 1 / 2) : ℝ) : ℂ) * Complex.I)‖ ≤
      Real.exp ((2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) -
        2 * Real.pi * u * (2 * (m : ℝ) + 1 / 2)) * plattScalarCMajorant m k t₀ h := by
  have hi := integral_mono (integrable_plattContourIntegrand_right m k hm ht₀ hh u).norm
    ((integrable_plattGammaWindow m k hm ht₀ hh).const_mul
      ((2 * Real.pi) ^ k * Real.exp ((2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) -
        2 * Real.pi * u * (2 * (m : ℝ) + 1 / 2))))
    (norm_plattContourIntegrand_right_le m k t₀ h u)
  rw [integral_const_mul] at hi
  have hj : _ ≤ Real.exp ((2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) -
      2 * Real.pi * u * (2 * (m : ℝ) + 1 / 2)) * plattScalarC m k t₀ h :=
    (norm_integral_le_integral_norm _).trans (hi.trans_eq (by unfold plattScalarC; ring))
  exact hj.trans (mul_le_mul_of_nonneg_left (plattScalarC_le_majorant m k hm ht₀ hh)
    (Real.exp_pos _).le)

/-- The negative-frequency integral has the corrected scalar and its own exact shift cost. -/
theorem norm_integral_plattContourIntegrand_left_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    ‖∫ v : ℝ, plattContourIntegrand k t₀ h u
      ((v : ℂ) + ((2 * (m : ℝ) + 3 / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
      Real.exp ((2 * (m : ℝ) + 3 / 2) ^ 2 / (2 * h ^ 2) +
        2 * Real.pi * u * (2 * (m : ℝ) + 3 / 2)) *
          (plattNegativeGammaFactor m * plattScalarCMajorant m k t₀ h) := by
  have hi : (∫ v : ℝ, ‖plattContourIntegrand k t₀ h u
      ((v : ℂ) + ((2 * (m : ℝ) + 3 / 2 : ℝ) : ℂ) * Complex.I)‖) =
      Real.exp ((2 * (m : ℝ) + 3 / 2) ^ 2 / (2 * h ^ 2) +
        2 * Real.pi * u * (2 * (m : ℝ) + 3 / 2)) * plattNegativeScalarC m k t₀ h := by
    simp_rw [norm_plattContourIntegrand_left]
    rw [integral_const_mul]
    unfold plattNegativeScalarC
    ring
  exact ((norm_integral_le_integral_norm _).trans_eq hi).trans
    (mul_le_mul_of_nonneg_left (plattNegativeScalarC_le_majorant m k hm ht₀ hh)
      (Real.exp_pos _).le)

end PrimeFactorUnimodality
