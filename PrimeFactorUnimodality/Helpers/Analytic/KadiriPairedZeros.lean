import PrimeFactorUnimodality.Helpers.Analytic.KadiriPairParameters
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedStechkinFormula

/-! # The paper-weight paired-zero inequality

The proved H2 condition, cubic error, and strip comparison establish the
smoothed Stechkin comparison for every height and every point of the full
closed strip. Conjugation identifies the analytic reflected pair with the
paper's same-height pair. Parameters satisfy exactly the symbolic κ₂/κ₃
bounds, so the result applies to the sharper Mossinghoff--Trudgian choices.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real
open scoped ComplexConjugate

/-- A real source gives the same shifted real contribution at conjugate points. -/
theorem smoothedLaplaceDifference_conj (f : ℝ → ℝ) (d κ δ : ℝ) (s : ℂ) :
    smoothedLaplaceDifference f d κ δ (conj s) = smoothedLaplaceDifference f d κ δ s := by
  unfold smoothedLaplaceDifference
  rw [show conj s + (δ : ℂ) = conj (s + (δ : ℂ)) by simp,
    finiteLaplace_conj_real, finiteLaplace_conj_real]
  rfl

/-- Uniform smoothed pair comparison on the entire closed strip, with no height restriction. -/
theorem kadiriWeight_pair_nonneg {θ η η₀ r₀ r δ κ x : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hη₀ : η ≤ η₀)
    (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hr₁ : r ≤ 1) (hδ : 0 < δ) (hκ : 0 ≤ κ)
    (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ r₀ δ) (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ r₀ δ)
    (hx₀ : 0 ≤ x) (hxr : x ≤ r) (y : ℝ) :
    0 ≤ smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        ((x : ℂ) + (y : ℂ) * I) +
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((r - x : ℝ) : ℂ) + (y : ℂ) * I) := by
  obtain ⟨hP₂, hP₀⟩ := kadiriPair_coefficients hθ hη hη₀ hr₀ hr hr₁ hδ hκ hκ₂ hκ₃
  let z : ℂ := (x : ℂ) + (y : ℂ) * I
  have hp := kadiriWeight_reflected_pair_nonneg hθ hη (hr₀.trans_le hr) hδ hκ hP₂ hP₀
    (z := z) (by simpa [z] using hx₀) (by simpa [z] using hxr)
  have hconj : conj ((r : ℂ) - z) = ((r - x : ℝ) : ℂ) + (y : ℂ) * I := by
    apply Complex.ext <;> simp [z]
  have heq := smoothedLaplaceDifference_conj (kadiriWeight θ η)
    (kadiriWeightSupport θ η) κ δ ((r : ℂ) - z)
  rw [← hconj, heq]
  unfold smoothedLaplaceDifference
  simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hp
  change 0 ≤ _ - _ + (_ - _)
  linarith

/-- Kadiri's paired-zero inequality in the paper's `σ, β, y` coordinates, including both edges. -/
theorem kadiriWeight_paired_zero_nonneg {θ η η₀ σ₀ σ β δ κ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 < η) (hη₀ : η ≤ η₀)
    (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ) (hσ₁ : σ ≤ 1) (hδ : 0 < δ) (hκ : 0 ≤ κ)
    (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ (2 * σ₀ - 1) δ)
    (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ (2 * σ₀ - 1) δ)
    (hβ₀ : 1 - σ ≤ β) (hβ₁ : β ≤ σ) (y : ℝ) :
    0 ≤ smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ - β : ℝ) : ℂ) + (y : ℂ) * I) +
      smoothedLaplaceDifference (kadiriWeight θ η) (kadiriWeightSupport θ η) κ δ
        (((σ - 1 + β : ℝ) : ℂ) + (y : ℂ) * I) := by
  have hp := kadiriWeight_pair_nonneg hθ hη hη₀ (r := 2 * σ - 1)
    (by linarith : 0 < 2 * σ₀ - 1) (by linarith) (by linarith) hδ hκ hκ₂ hκ₃
    (x := σ - β) (by linarith) (by linarith) y
  rwa [show 2 * σ - 1 - (σ - β) = σ - 1 + β by ring] at hp

end

end PrimeFactorUnimodality
