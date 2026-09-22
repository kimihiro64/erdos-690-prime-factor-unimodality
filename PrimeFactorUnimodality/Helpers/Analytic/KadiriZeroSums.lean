import PrimeFactorUnimodality.Helpers.Analytic.KadiriPairedZeros
import PrimeFactorUnimodality.Helpers.Analytic.KadiriZeroSummability
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiDivisorPairing

/-! # Discarding central xi-zero pairs in the smoothed explicit formula

Kadiri's paired comparison applies to the central closed strip. The actual
divisor reflection and absolute summability pass it through the complete
series, including multiplicities and critical-line zeros. The complementary
outer-strip series remains explicit: this step does not assume that every
zero lies in the central strip, nor that the remaining series is nonnegative.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real
open scoped ComplexConjugate

/-- The central strip on which the smoothed pair comparison applies. -/
def kadiriCentralStrip (σ : ℝ) (z : ℂ) : Prop := 1 - σ ≤ z.re ∧ z.re ≤ σ

/-- Same-height reflection preserves the entire central strip, including its boundary. -/
theorem kadiriCentralStrip_reflection (σ : ℝ) (z : ℂ) :
    kadiriCentralStrip σ z ↔ kadiriCentralStrip σ (1 - conj z) := by
  simp only [kadiriCentralStrip, sub_re, one_re, conj_re]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

variable {θ η η₀ σ₀ σ δ κ : ℝ}
  (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hη₀ : η ≤ η₀)
  (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσ₁ : σ ≤ 1) (hδ : 0 < δ) (hκ : 0 ≤ κ)
  (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ (2 * σ₀ - 1) δ)
  (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ (2 * σ₀ - 1) δ)

include hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃

/-- The paper comparison written directly at an arbitrary central-strip complex zero value. -/
theorem kadiriWeight_zero_pair_nonneg {ρ : ℂ} (hρ : kadiriCentralStrip σ ρ) (t : ℝ) :
    0 ≤ smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ : ℂ) + (t : ℂ) * I) - ρ) +
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ : ℂ) + (t : ℂ) * I) - (1 - conj ρ)) := by
  have hp := kadiriWeight_paired_zero_nonneg hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃
    hρ.1 hρ.2 (t - ρ.im)
  have h₁ : ((σ - ρ.re : ℝ) : ℂ) + ((t - ρ.im : ℝ) : ℂ) * I =
      ((σ : ℂ) + (t : ℂ) * I) - ρ := by
    apply Complex.ext <;> simp
  have h₂ : ((σ - 1 + ρ.re : ℝ) : ℂ) + ((t - ρ.im : ℝ) : ℂ) * I =
      ((σ : ℂ) + (t : ℂ) * I) - (1 - conj ρ) := by
    apply Complex.ext <;> simp
    ring
  rwa [h₁, h₂] at hp

/-- The complete central-strip divisor contribution is nonnegative at every height. -/
theorem kadiriWeight_central_zero_sum_nonneg (t : ℝ) :
    0 ≤ ∑' p : {p : RiemannXiDivisorZeroIndex //
        kadiriCentralStrip σ (riemannXiDivisorZeroValue p)},
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ : ℂ) + (t : ℂ) * I) - riemannXiDivisorZeroValue p.1) := by
  exact tsum_xi_divisor_subtype_nonneg (kadiriCentralStrip σ)
    (G := fun ρ => smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η)
      κ δ (((σ : ℂ) + (t : ℂ) * I) - ρ))
    (kadiriCentralStrip_reflection σ)
    (summable_kadiriWeight_zero_difference hθ hη κ δ ((σ : ℂ) + (t : ℂ) * I))
    (fun _ hρ => kadiriWeight_zero_pair_nonneg hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃ hρ t)

/-- Only the outer-strip contribution remains when central nonnegative pairs are discarded. -/
theorem kadiriWeight_outer_zero_sum_le (t : ℝ) :
    (∑' p : {p : RiemannXiDivisorZeroIndex //
        ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue p)},
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ : ℂ) + (t : ℂ) * I) - riemannXiDivisorZeroValue p.1)) ≤
      ∑' p : RiemannXiDivisorZeroIndex,
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (t : ℂ) * I) - riemannXiDivisorZeroValue p) := by
  exact tsum_xi_divisor_compl_le (kadiriCentralStrip σ)
    (G := fun ρ => smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η)
      κ δ (((σ : ℂ) + (t : ℂ) * I) - ρ))
    (kadiriCentralStrip_reflection σ)
    (summable_kadiriWeight_zero_difference hθ hη κ δ ((σ : ℂ) + (t : ℂ) * I))
    (fun _ hρ => kadiriWeight_zero_pair_nonneg hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃ hρ t)

/-- Keep one actual off-critical zero pair, plus the entire outer-strip remainder. -/
theorem kadiriWeight_retained_pair_add_outer_le (p : RiemannXiDivisorZeroIndex)
    (hp : kadiriCentralStrip σ (riemannXiDivisorZeroValue p))
    (hne : (riemannXiDivisorZeroValue p).re ≠ 1 / 2) (t : ℝ) :
    smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ : ℂ) + (t : ℂ) * I) - riemannXiDivisorZeroValue p) +
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ : ℂ) + (t : ℂ) * I) - (1 - conj (riemannXiDivisorZeroValue p))) +
      (∑' q : {q : RiemannXiDivisorZeroIndex //
          ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue q)},
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (t : ℂ) * I) - riemannXiDivisorZeroValue q.1)) ≤
      ∑' q : RiemannXiDivisorZeroIndex,
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (t : ℂ) * I) - riemannXiDivisorZeroValue q) := by
  exact xi_divisor_pair_add_tsum_compl_le (kadiriCentralStrip σ)
    (G := fun ρ => smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η)
      κ δ (((σ : ℂ) + (t : ℂ) * I) - ρ))
    (kadiriCentralStrip_reflection σ)
    (summable_kadiriWeight_zero_difference hθ hη κ δ ((σ : ℂ) + (t : ℂ) * I))
    (fun _ hρ => kadiriWeight_zero_pair_nonneg hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃ hρ t)
    p hp hne

/-- Nonnegative trigonometric coefficients preserve the central-strip elimination. -/
theorem kadiriWeight_weighted_outer_zero_sum_le {ι : Type*} (S : Finset ι) (a k : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (t : ℝ) :
    (∑ i ∈ S, a i * ∑' p : {p : RiemannXiDivisorZeroIndex //
        ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue p)},
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ : ℂ) + (k i * t : ℝ) * I) - riemannXiDivisorZeroValue p.1)) ≤
      ∑ i ∈ S, a i * ∑' p : RiemannXiDivisorZeroIndex,
        smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
          (((σ : ℂ) + (k i * t : ℝ) * I) - riemannXiDivisorZeroValue p) := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (kadiriWeight_outer_zero_sum_le hθ hη hη₀ hσ₀ hσ hσ₁ hδ hκ hκ₂ hκ₃ (k i * t)) (ha i hi)

end

end PrimeFactorUnimodality
