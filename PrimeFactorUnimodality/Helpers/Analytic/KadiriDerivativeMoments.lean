import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeightedRemainder
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ExpMoments

/-! # Four-moment majorants for the exact derivative mass

These are the `Mₖ(θ)` and `M*(z,θ)` in Mossinghoff--Trudgian section 4.
The analytic comparison is uniform on its entire parameter domain; only
a single exponential endpoint bound and the moment values need numerical
checking. Those finite inputs are not assumed to have been certified here.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real

/-- The unscaled absolute second-derivative moment of any natural degree. -/
def kadiriDerivativeMoment (θ : ℝ) (n : ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..kadiriSupport θ, u ^ n * |kadiriKernel₂ θ u|

/-- All derivative moments are nonnegative on the actual support. -/
theorem kadiriDerivativeMoment_nonneg {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (n : ℕ) :
    0 ≤ kadiriDerivativeMoment θ n := by
  apply intervalIntegral.integral_nonneg (kadiriSupport_pos hθ).le
  intro u hu
  exact mul_nonneg (pow_nonneg hu.1 n) (abs_nonneg _)

/-- The cubic majorant reduces the exact mass to four actual kernel moments. -/
theorem kadiriDerivativeMass_le_moments {θ z y C : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hz : z ≤ 0) (hy : 0 < y)
    (hzy : -z * kadiriSupport θ ≤ y)
    (hend : Real.exp y ≤ 1 + y + y ^ 2 / 2 + C * y ^ 3) :
    kadiriDerivativeMass θ z ≤
      kadiriDerivativeMoment θ 0 - z * kadiriDerivativeMoment θ 1 +
        z ^ 2 / 2 * kadiriDerivativeMoment θ 2 - C * z ^ 3 * kadiriDerivativeMoment θ 3 := by
  simpa only [kadiriDerivativeMass, kadiriDerivativeMoment, pow_zero, one_mul, pow_one] using
    intervalIntegral.integral_mul_exp_le_cubic_moments (kadiriSupport_pos hθ).le
      (continuous_kadiriKernel₂ θ).abs.continuousOn (fun u _ => abs_nonneg _) hz hy hzy hend

/-- The paper's exact cubic moment majorant, with denominator `3.45`. -/
def kadiriDerivativeMassMajorant (θ z : ℝ) : ℝ :=
  kadiriDerivativeMoment θ 0 - kadiriDerivativeMoment θ 1 * z +
    kadiriDerivativeMoment θ 2 * z ^ 2 / 2 - kadiriDerivativeMoment θ 3 * z ^ 3 / (345 / 100)

/-- One exponential endpoint check suffices for the paper's moment majorant on the full interval. -/
theorem kadiriDerivativeMass_le_majorant {θ z y : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hz : z ≤ 0) (hy : 0 < y)
    (hzy : -z * kadiriSupport θ ≤ y)
    (hend : Real.exp y ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / (345 / 100)) :
    kadiriDerivativeMass θ z ≤ kadiriDerivativeMassMajorant θ z := by
  have he : Real.exp y ≤ 1 + y + y ^ 2 / 2 + (100 / 345) * y ^ 3 := by
    convert hend using 1
    ring
  have h := kadiriDerivativeMass_le_moments hθ hz hy hzy he
  convert h using 1
  unfold kadiriDerivativeMassMajorant
  ring

/-- For nonpositive `z` all four moment coefficients are nonnegative, so upper bounds are used. -/
theorem kadiriDerivativeMassMajorant_le_of_moment_bounds {θ z B₀ B₁ B₂ B₃ : ℝ}
    (hz : z ≤ 0) (h₀ : kadiriDerivativeMoment θ 0 ≤ B₀)
    (h₁ : kadiriDerivativeMoment θ 1 ≤ B₁) (h₂ : kadiriDerivativeMoment θ 2 ≤ B₂)
    (h₃ : kadiriDerivativeMoment θ 3 ≤ B₃) :
    kadiriDerivativeMassMajorant θ z ≤
      B₀ - B₁ * z + B₂ * z ^ 2 / 2 - B₃ * z ^ 3 / (345 / 100) := by
  have h₁' := mul_le_mul_of_nonneg_right h₁ (neg_nonneg.mpr hz)
  have h₂' := mul_le_mul_of_nonneg_right h₂ (div_nonneg (sq_nonneg z) (by norm_num : (0 : ℝ) ≤ 2))
  have h₃' := mul_le_mul_of_nonneg_right h₃
    (div_nonneg (pow_nonneg (neg_nonneg.mpr hz) 3) (by norm_num : (0 : ℝ) ≤ 345 / 100))
  unfold kadiriDerivativeMassMajorant
  nlinarith only [h₀, h₁', h₂', h₃']

/-- The four-moment bound feeds the actual weight's arbitrary-vertical-line remainder. -/
theorem abs_re_kadiriWeight_laplace_sub_pole_le_majorant_im {θ η z y : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hz : z ≤ 0) (hy : 0 < y)
    (hzy : -z * kadiriSupport θ ≤ y)
    (hend : Real.exp y ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / (345 / 100))
    {s : ℂ} (hs : z ≤ s.re / η) (hi : s.im ≠ 0) :
    |(finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) s).re -
      kadiriWeight θ η 0 * s.re / (s.re ^ 2 + s.im ^ 2)| ≤
        η ^ 2 * kadiriDerivativeMassMajorant θ z / s.im ^ 2 := by
  exact (abs_re_kadiriWeight_laplace_sub_pole_le_mass_im hθ hη hs hi).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (kadiriDerivativeMass_le_majorant hθ hz hy hzy hend) (sq_nonneg η))
      (sq_nonneg _))

end

end PrimeFactorUnimodality
