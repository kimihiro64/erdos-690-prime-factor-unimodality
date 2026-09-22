import PrimeFactorUnimodality.Helpers.Analytic.KadiriExplicitMaster

/-! # Explicit Gamma estimates without asymptotic hypotheses

Check the complex approximation, the zero-length reciprocal sum, both
extreme subtraction weights, signed heights, and arbitrary polynomial degree.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter Real
open scoped Topology

example (z : ℂ) : Tendsto (fun n : ℕ => Complex.log (z + n) -
    (Real.log ((n : ℝ) + 1) : ℂ)) atTop (𝓝 0) :=
  Complex.tendsto_log_add_nat_sub_log_nat_add_one z

example {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    ‖(∑ k ∈ Finset.range (N + 1), (z + (k : ℂ))⁻¹) -
      (Complex.log (z + N) - Complex.log z)‖ ≤ 1 / z.re :=
  norm_sum_inv_add_sub_log_le hz N

example {z : ℂ} (hz : 0 < z.re) : ‖z⁻¹‖ ≤ 1 / z.re := by
  simpa using norm_sum_inv_add_sub_log_le hz 0

example {z : ℂ} (hz : 0 < z.re) : ‖digamma z - Complex.log z‖ ≤ 1 / z.re :=
  norm_digamma_sub_log_le_inv_re hz

example {z : ℂ} (hz : 0 < z.re) :
    Real.log ‖z‖ - 1 / z.re ≤ (digamma z).re := by
  have h := (abs_le.mp (abs_re_digamma_sub_log_norm_le hz)).1
  linarith

example (t : ℝ) : ‖digamma (1 + (t : ℂ) * I) - Complex.log (1 + (t : ℂ) * I)‖ ≤ 1 := by
  simpa using norm_digamma_sub_log_le_inv_re (z := 1 + (t : ℂ) * I) (by simp)

example {s : ℂ} (hs : 0 ≤ s.re) :
    smoothedGammaFactorDifference 0 0 s ≤
      (1 / 2 : ℝ) * (Real.log ‖s / 2 + 1‖ - Real.log π) + 1 / (s.re + 2) := by
  simpa using smoothedGammaFactorDifference_le_log_norm (κ := 0) (δ := 0) le_rfl le_rfl hs

example {s : ℂ} (hs : 0 ≤ s.re) {δ : ℝ} (hδ : 0 ≤ δ) :
    smoothedGammaFactorDifference 1 δ s ≤ 2 / (s.re + 2) := by
  convert! smoothedGammaFactorDifference_le_log_norm (κ := 1) (by norm_num) hδ hs using 1
  norm_num

example {θ η σ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)
    (hσ : 1 / 2 < σ) (t : ℝ) :
    ‖smoothedGammaRemainder (fun u => (kadiriWeight₂ θ η u : ℂ))
      (kadiriWeightSupport θ η) ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        η ^ 3 * (-kadiriKernel₂ θ 0) / 4 :=
  norm_kadiriWeight_gammaRemainder_le hθ hη (by simpa using hσ)

example {θ η κ δ σ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)
    (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hσ : 1 / 2 < σ) :
    |smoothedGammaRemainderDifference (fun u => (kadiriWeight₂ θ η u : ℂ))
      (kadiriWeightSupport θ η) κ δ (σ : ℂ)| ≤
        (1 + κ) * η ^ 3 * (-kadiriKernel₂ θ 0) / 4 :=
  abs_kadiriWeight_gammaRemainderDifference_le hθ hη hκ hδ hσ

example {κ δ σ : ℝ} (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1) (hδ : 0 ≤ δ)
    (hσ : 0 ≤ σ) (hσ₂ : σ ≤ 2) (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) (t : ℝ) :
    (∑ i ∈ Finset.range (n + 1), a i * smoothedGammaFactorDifference κ δ
      ((σ : ℂ) + ((i : ℝ) * t : ℝ) * I)) ≤
      ∑ i ∈ Finset.range (n + 1), a i * smoothedGammaFactorMajorant κ σ ((i : ℝ) * t) :=
  sum_smoothedGammaFactorDifference_le hκ hκ₁ hδ hσ hσ₂ _ a (fun i => (i : ℝ)) ha t

example {θ η κ δ σ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η)
    (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hσ : 1 / 2 < σ) (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) (t : ℝ) :
    (∑ i ∈ Finset.range (n + 1), a i * smoothedGammaRemainderDifference
      (fun u => (kadiriWeight₂ θ η u : ℂ)) (kadiriWeightSupport θ η) κ δ
        ((σ : ℂ) + ((i : ℝ) * t : ℝ) * I)) ≤
      (∑ i ∈ Finset.range (n + 1), a i) * ((1 + κ) * η ^ 3 * (-kadiriKernel₂ θ 0) / 4) :=
  sum_kadiriWeight_gammaRemainderDifference_le hθ hη hκ hδ hσ _ a (fun i => (i : ℝ)) ha t

end

end PrimeFactorUnimodality.Tests
