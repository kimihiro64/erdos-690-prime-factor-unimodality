import PrimeFactorUnimodality.Helpers.Analytic.KadiriLaplaceBounds
import PrimeFactorUnimodality.Helpers.Analytic.KadiriStechkin

/-! # Symbolic positivity, derivative-bound, and actual-weight master regressions

The angle, scale, support point, and polynomial parameters remain arbitrary.
These checks do not replace a universal statement by finitely many samples.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Real Set

example {f : ℝ → ℝ} (hf : Continuous f) {a b u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ b - a) :
    |∫ v in a..b - u, f v * f (v + u)| ≤ ∫ v in a..b, f v ^ 2 :=
  intervalIntegral.abs_integral_mul_translate_le_integral_sq hf hu hu'

example {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (u : ℝ) :
    kadiriKernel θ u = (1 / Real.cos θ ^ 4) *
      ∫ v in (θ / Real.tan θ)..(-θ / Real.tan θ - u),
        (Real.cos (Real.tan θ * v) - Real.cos θ) *
          (Real.cos (Real.tan θ * (v + u)) - Real.cos θ) :=
  kadiriKernel_eq_cosineCorrelation hθ u

example {θ η : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (u : ℝ) :
    0 ≤ kadiriWeight θ η u := kadiriWeight_nonneg hθ hη u

example {θ u : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hu : u ∈ Icc 0 (kadiriSupport θ)) :
    |kadiriKernel₂ θ u| ≤ -kadiriKernel₂ θ 0 := abs_kadiriKernel₂_le_neg_zero hθ hu

example {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) :
    IsGreatest ((fun u => |kadiriKernel₂ θ u|) '' Icc 0 (kadiriSupport θ))
      (-kadiriKernel₂ θ 0) := isGreatest_abs_kadiriKernel₂ hθ

example {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) :
    -kadiriKernel₂ θ 0 = (Real.tan θ ^ 2 / Real.cos θ ^ 4) *
      (-θ / Real.tan θ + Real.cos θ ^ 2) := neg_kadiriKernel₂_zero_eq hθ

example {θ η u : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)
    (hu : u ∈ Icc 0 (kadiriWeightSupport θ η)) :
    ‖(kadiriWeight₂ θ η u : ℂ)‖ ≤ η ^ 3 * (-kadiriKernel₂ θ 0) :=
  norm_kadiriWeight₂_le hθ hη hu

example {θ η : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) {s : ℂ} (hs : 0 < s.re) :
    |(finiteLaplace (fun u => (kadiriWeight θ η u : ℂ)) (kadiriWeightSupport θ η) s).re -
      kadiriWeight θ η 0 * s.re / (s.re ^ 2 + s.im ^ 2)| ≤
        η ^ 3 * (-kadiriKernel₂ θ 0) / (s.re * (s.re ^ 2 + s.im ^ 2)) :=
  abs_re_kadiriWeight_laplace_sub_pole_le hθ hη hs

example {θ η : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)
    {ι : Type*} (S : Finset ι) (a k : ι → ℝ)
    {σ κ δ : ℝ} (hσ : 1 / 2 < σ) (hδ : 0 ≤ δ) (hκ : κ ≤ 1) (t : ℝ)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ S, a i * Real.cos (k i * u)) :
    0 ≤ (∑ i ∈ S, a i * smoothedLaplaceDifference (kadiriWeight θ η)
        (kadiriWeightSupport θ η) κ δ (((σ : ℂ) + (k i * t : ℝ) * I) - 1)) -
      (∑' p : RiemannXiDivisorZeroIndex, ∑ i ∈ S, a i *
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (k i * t : ℝ) * I) - riemannXiDivisorZeroValue p)) +
      kadiriWeight θ η 0 * (∑ i ∈ S, a i * smoothedGammaFactorDifference κ δ
        ((σ : ℂ) + (k i * t : ℝ) * I)) +
      ∑ i ∈ S, a i * smoothedGammaRemainderDifference (fun u => (kadiriWeight₂ θ η u : ℂ))
        (kadiriWeightSupport θ η) κ δ ((σ : ℂ) + (k i * t : ℝ) * I) :=
  kadiriWeight_master_nonneg hθ hη S a k hσ hδ hκ t hpoly

end

end PrimeFactorUnimodality.Tests
