import PrimeFactorUnimodality.Helpers.Analytic.KadiriLaplaceBounds
import PrimeFactorUnimodality.Helpers.Analytic.KadiriLaplacePositivity
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.PairedStrip
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson.ThreeKernel

/-! # The smoothed paired-zero comparison from two coefficient inequalities

H2 and the sharp cubic transform error give three rational kernels on the
imaginary edge. Two scalar coefficient inequalities make their difference
nonnegative at every height. The entire reflected transform is bounded on
the strip, so the real-part minimum principle extends this to its interior.
This proves the analytic reduction behind Kadiri proposition 4.2 without
treating a quotient of harmonic functions as harmonic.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real Set

/-- Numerator of the lower rational bound for the actual paper weight. -/
def kadiriPairLower (θ η x : ℝ) : ℝ :=
  kadiriWeight θ η 0 * x - η ^ 3 * (-kadiriKernel₂ θ 0) / x

/-- Numerator of the upper rational bound for the actual paper weight. -/
def kadiriPairUpper (θ η x : ℝ) : ℝ :=
  kadiriWeight θ η 0 * x + η ^ 3 * (-kadiriKernel₂ θ 0) / x

/-- The two endpoint coefficients imply comparison on the whole imaginary boundary. -/
theorem kadiriWeight_pair_boundary_nonneg {θ η r δ κ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hr : 0 < r) (hδ : 0 < δ) (hκ : 0 ≤ κ)
    (hP₂ : 0 ≤ kadiriPairLower θ η r -
      κ * (kadiriPairUpper θ η δ + kadiriPairUpper θ η (r + δ)))
    (hP₀ : 0 ≤ kadiriPairLower θ η r * δ ^ 2 * (r + δ) ^ 2 -
      κ * r ^ 2 * (kadiriPairUpper θ η δ * (r + δ) ^ 2 +
        kadiriPairUpper θ η (r + δ) * δ ^ 2))
    {z : ℂ} (hz : z.re = 0) :
    0 ≤ (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) z +
      finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
        (kadiriWeightSupport θ η) ((r : ℂ) - z) -
      (κ : ℂ) * (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
        (kadiriWeightSupport θ η) (z + δ) +
      finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
        (kadiriWeightSupport θ η) ((r : ℂ) - z + δ))).re := by
  have h₀ := re_kadiriWeight_laplace_nonneg hθ hη (s := z) (by rw [hz])
  have h₁ := (re_kadiriWeight_laplace_bounds hθ hη (s := (r : ℂ) - z)
    (by simpa [hz] using hr)).1
  have h₂ := (re_kadiriWeight_laplace_bounds hθ hη (s := z + δ)
    (by simpa [hz] using hδ)).2
  have h₃ := (re_kadiriWeight_laplace_bounds hθ hη (s := (r : ℂ) - z + δ)
    (by simpa [hz] using add_pos hr hδ)).2
  have hC : 0 ≤ kadiriPairUpper θ η (r + δ) := by
    unfold kadiriPairUpper
    exact add_nonneg (mul_nonneg (kadiriWeight_zero_pos hθ hη).le (add_pos hr hδ).le)
      (div_nonneg (mul_nonneg (pow_nonneg hη.le 3) (neg_kadiriKernel₂_zero_nonneg hθ))
        (add_pos hr hδ).le)
  have hp := threeKernel_nonneg hr hδ (by linarith) (by linarith) hκ hC hP₂ hP₀ z.im
  simp only [sub_re, add_re, ofReal_re, sub_im, add_im, ofReal_im, hz,
    sub_zero, zero_sub, zero_add, add_zero, neg_sq] at h₁ h₂ h₃
  change kadiriPairLower θ η r / (r ^ 2 + z.im ^ 2) ≤ _ at h₁
  change _ ≤ kadiriPairUpper θ η δ / (δ ^ 2 + z.im ^ 2) at h₂
  change _ ≤ kadiriPairUpper θ η (r + δ) / ((r + δ) ^ 2 + z.im ^ 2) at h₃
  have hu := mul_le_mul_of_nonneg_left (add_le_add h₂ h₃) hκ
  simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  linarith

/-- The actual smoothed comparison throughout the closed strip, at every complex height. -/
theorem kadiriWeight_reflected_pair_nonneg {θ η r δ κ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hr : 0 < r) (hδ : 0 < δ) (hκ : 0 ≤ κ)
    (hP₂ : 0 ≤ kadiriPairLower θ η r -
      κ * (kadiriPairUpper θ η δ + kadiriPairUpper θ η (r + δ)))
    (hP₀ : 0 ≤ kadiriPairLower θ η r * δ ^ 2 * (r + δ) ^ 2 -
      κ * r ^ 2 * (kadiriPairUpper θ η δ * (r + δ) ^ 2 +
        kadiriPairUpper θ η (r + δ) * δ ^ 2))
    {z : ℂ} (hz₀ : 0 ≤ z.re) (hzr : z.re ≤ r) :
    0 ≤ (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) z +
      finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
        (kadiriWeightSupport θ η) ((r : ℂ) - z) -
      (κ : ℂ) * (finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
        (kadiriWeightSupport θ η) (z + δ) +
      finiteLaplace (fun u => (kadiriWeight θ η u : ℂ))
        (kadiriWeightSupport θ η) ((r : ℂ) - z + δ))).re := by
  exact re_finiteLaplace_reflected_pair_nonneg (kadiriWeightSupport_pos hθ hη).le
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_kadiriWeight θ η)) hr hδ.le
    (fun _ hz => kadiriWeight_pair_boundary_nonneg hθ hη hr hδ hκ hP₂ hP₀ hz) hz₀ hzr

end

end PrimeFactorUnimodality
