import PrimeFactorUnimodality.Helpers.Analytic.KadiriPairedStrip
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Poisson.ThreeKernelUniform

/-! # Exact uniform parameters for the smoothed paired-zero comparison

These are the two bounds in Kadiri (36)--(37), also used on page 5 of
Mossinghoff--Trudgian, <https://arxiv.org/pdf/1410.3926>. The parameter `r₀`
is `2*σ₀-1`; the source value and derivative constant are the actual proved
kernel values. The bounds hold uniformly for `r₀ ≤ r ≤ 1` and `0 < η ≤ η₀`.
No rounded numerical choice of the parameters is assumed here.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The leading-coefficient parameter bound, with `r₀ = 2*σ₀-1`. -/
def kadiriKappa₂ (θ η₀ r₀ δ : ℝ) : ℝ :=
  (kadiriKernel θ 0 * r₀ - η₀ ^ 2 * (-kadiriKernel₂ θ 0) / r₀) /
    ((1 + 2 * δ) * kadiriKernel θ 0 +
      (1 / δ + 1 / (δ + r₀)) * (η₀ ^ 2 * (-kadiriKernel₂ θ 0)))

/-- The constant-coefficient parameter bound, retaining the paper's exact denominators. -/
def kadiriKappa₃ (θ η₀ r₀ δ : ℝ) : ℝ :=
  (kadiriKernel θ 0 * r₀ - η₀ ^ 2 * (-kadiriKernel₂ θ 0) / r₀) /
    ((1 / δ + (1 + δ) / (δ + r₀) ^ 2) * kadiriKernel θ 0 +
      (1 / δ ^ 3 + 1 / (δ + r₀) ^ 3) * (η₀ ^ 2 * (-kadiriKernel₂ θ 0)))

/-- The paper's two parameter bounds imply both boundary coefficients for every allowed scale. -/
theorem kadiriPair_coefficients {θ η η₀ r₀ r δ κ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hη₀ : η ≤ η₀)
    (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hr₁ : r ≤ 1) (hδ : 0 < δ) (hκ : 0 ≤ κ)
    (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ r₀ δ) (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ r₀ δ) :
    0 ≤ kadiriPairLower θ η r -
      κ * (kadiriPairUpper θ η δ + kadiriPairUpper θ η (r + δ)) ∧
    0 ≤ kadiriPairLower θ η r * δ ^ 2 * (r + δ) ^ 2 -
      κ * r ^ 2 * (kadiriPairUpper θ η δ * (r + δ) ^ 2 +
        kadiriPairUpper θ η (r + δ) * δ ^ 2) := by
  have hg := kadiriKernel_zero_pos hθ
  have hm := neg_kadiriKernel₂_zero_nonneg hθ
  have hb := add_pos hδ hr₀
  have hden₂ : 0 < (1 + 2 * δ) * kadiriKernel θ 0 +
      (1 / δ + 1 / (δ + r₀)) * (η₀ ^ 2 * (-kadiriKernel₂ θ 0)) := by positivity
  have hden₃ : 0 < (1 / δ + (1 + δ) / (δ + r₀) ^ 2) * kadiriKernel θ 0 +
      (1 / δ ^ 3 + 1 / (δ + r₀) ^ 3) * (η₀ ^ 2 * (-kadiriKernel₂ θ 0)) := by positivity
  have heE : η ^ 2 * (-kadiriKernel₂ θ 0) ≤ η₀ ^ 2 * (-kadiriKernel₂ θ 0) :=
    mul_le_mul_of_nonneg_right (by nlinarith) hm
  have hc := threeKernel_coefficients_of_uniform_bounds hg.le
    (mul_nonneg (sq_nonneg η) hm) heE hr₀ hr hr₁ hδ hκ
    ((le_div_iff₀ hden₂).mp hκ₂) ((le_div_iff₀ hden₃).mp hκ₃)
  have hzero : kadiriWeight θ η 0 = η * kadiriKernel θ 0 := by
    rw [kadiriWeight_of_mem ⟨le_rfl, (kadiriWeightSupport_pos hθ hη).le⟩, mul_zero]
  have hl (x : ℝ) : kadiriPairLower θ η x =
      η * (kadiriKernel θ 0 * x - (η ^ 2 * (-kadiriKernel₂ θ 0)) / x) := by
    unfold kadiriPairLower
    rw [hzero]
    ring
  have hu (x : ℝ) : kadiriPairUpper θ η x =
      η * (kadiriKernel θ 0 * x + (η ^ 2 * (-kadiriKernel₂ θ 0)) / x) := by
    unfold kadiriPairUpper
    rw [hzero]
    ring
  simp only [hl, hu]
  constructor
  · convert mul_nonneg hη.le hc.1 using 1
    ring
  · convert mul_nonneg hη.le hc.2 using 1
    ring

end

end PrimeFactorUnimodality
