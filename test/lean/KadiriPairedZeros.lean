import PrimeFactorUnimodality.Helpers.Analytic.KadiriPairedZeros

/-! # Uniform paired-zero comparison regressions

The tests retain arbitrary heights, both closed-strip edges, and the exact
paper parameters. A separate rational example exercises a nonzero error
constant and a varying scale, without assuming the coefficient inequalities.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Real
open scoped ComplexConjugate

example (f : ℝ → ℝ) (d : ℝ) (s : ℂ) :
    finiteLaplace (fun u => (f u : ℂ)) d (conj s) =
      conj (finiteLaplace (fun u => (f u : ℂ)) d s) :=
  finiteLaplace_conj_real f d s

example {f : ℝ → ℂ} {d : ℝ} (hd : 0 ≤ d) (hf : ContinuousOn f (Set.Icc 0 d)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, 0 ≤ s.re → ‖finiteLaplace f d s‖ ≤ M :=
  exists_bound_finiteLaplace_rightHalfPlane hd hf

example {r : ℝ} (hr : 99 / 100 ≤ r) (hr₁ : r ≤ 1) (y : ℝ) :
    0 ≤ (r - (1 / 10000) / r) / (r ^ 2 + y ^ 2) -
      (44 / 100) *
        (((62 / 100) + (1 / 10000) / (62 / 100)) / ((62 / 100) ^ 2 + y ^ 2) +
          ((r + (62 / 100)) + (1 / 10000) / (r + (62 / 100))) /
            ((r + (62 / 100)) ^ 2 + y ^ 2)) := by
  have hc := threeKernel_coefficients_of_uniform_bounds (g := 1) (e := 1 / 10000)
    (E := 1 / 10000) (r₀ := 99 / 100) (r := r) (δ := 62 / 100) (κ := 44 / 100)
    (by norm_num) (by norm_num) le_rfl (by norm_num) hr hr₁ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hrpos : 0 < r := by linarith
  simpa only [one_mul] using threeKernel_nonneg hrpos (d := 62 / 100)
    (b := r + 62 / 100) (by norm_num) (by linarith) (by linarith) (by norm_num)
    (by positivity : 0 ≤ 1 * (r + 62 / 100) + (1 / 10000) / (r + 62 / 100)) hc.1 hc.2 y

variable {θ η η₀ σ₀ σ β δ κ : ℝ}
  (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hη₀ : η ≤ η₀)
  (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσ₁ : σ ≤ 1) (hδ : 0 < δ) (hκ : 0 ≤ κ)
  (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ (2 * σ₀ - 1) δ)
  (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ (2 * σ₀ - 1) δ)

example (hβ₀ : 1 - σ ≤ β) (hβ₁ : β ≤ σ) (y : ℝ) :
    0 ≤ smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ - β : ℝ) : ℂ) + (y : ℂ) * I) +
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ - 1 + β : ℝ) : ℂ) + (y : ℂ) * I) :=
  kadiriWeight_paired_zero_nonneg hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃ hβ₀ hβ₁ y

example (y : ℝ) :
    0 ≤ smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        ((y : ℂ) * I) +
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((2 * σ - 1 : ℝ) : ℂ) + (y : ℂ) * I) := by
  convert kadiriWeight_paired_zero_nonneg hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃
    (β := σ) (by linarith) le_rfl y using 1
  congr 2 <;> push_cast <;> ring

example (y : ℝ) :
    0 ≤ smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((2 * σ - 1 : ℝ) : ℂ) + (y : ℂ) * I) +
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        ((y : ℂ) * I) := by
  convert kadiriWeight_paired_zero_nonneg hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃
    (β := 1 - σ) le_rfl (by linarith) y using 1
  congr 2 <;> push_cast <;> ring

end

end PrimeFactorUnimodality.Tests
