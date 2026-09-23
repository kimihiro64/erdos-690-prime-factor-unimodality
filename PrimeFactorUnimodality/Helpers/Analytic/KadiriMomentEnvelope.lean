import PrimeFactorUnimodality.Helpers.Analytic.KadiriCorrectionEnvelope
import PrimeFactorUnimodality.Helpers.Analytic.KadiriDerivativeMoments

/-! # Four-moment substitution into the complete correction

Use the existing derivative-moment theorem, the proved harmonic tail
envelope, and the decreasing pole and Gamma residuals. The resulting
cubic expression has no derivative-mass integral. Its four moment bounds,
the exponential endpoint check, and the exact low-zero subtraction remain
explicit numerical inputs; they are not asserted to have been verified.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The explicit four-moment derivative-mass bound. -/
def kadiriMomentMassBound (z B₀ B₁ B₂ B₃ : ℝ) : ℝ :=
  B₀ - B₁ * z + B₂ * z ^ 2 / 2 - B₃ * z ^ 3 / (345 / 100)

/-- The existing moment theorem gives the stated numerical mass envelope. -/
theorem kadiriDerivativeMass_le_momentMassBound {θ z y B₀ B₁ B₂ B₃ : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hz : z ≤ 0) (hy : 0 < y)
    (hzy : -z * kadiriSupport θ ≤ y)
    (hend : Real.exp y ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / (345 / 100))
    (h₀ : kadiriDerivativeMoment θ 0 ≤ B₀) (h₁ : kadiriDerivativeMoment θ 1 ≤ B₁)
    (h₂ : kadiriDerivativeMoment θ 2 ≤ B₂) (h₃ : kadiriDerivativeMoment θ 3 ≤ B₃) :
    kadiriDerivativeMass θ z ≤ kadiriMomentMassBound z B₀ B₁ B₂ B₃ :=
  (kadiriDerivativeMass_le_majorant hθ hz hy hzy hend).trans
    (kadiriDerivativeMassMajorant_le_of_moment_bounds hz h₀ h₁ h₂ h₃)

/-- The complete cubic envelope after all analytic scalar substitutions. -/
def kadiriMomentCorrectionPolynomial (θ η η₀ σ₀ κ δ z H T B₀ B₁ B₂ B₃ q : ℝ)
    (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  kadiriCorrectionPolynomial θ η η₀ σ₀ κ δ (kadiriMomentMassBound z B₀ B₁ B₂ B₃)
    (kadiriPoleCoefficient S a T) (kadiriTailAffineConstant T H S a)
    (kadiriTailLogCoefficient T H S a) (kadiriGammaResidual κ σ₀ T S a) q S a

/-- The actual correction obeys the full moment-based cubic envelope at every valid height. -/
theorem kadiriBootstrapCorrection_le_momentPolynomial
    {θ η η₀ σ₀ σ κ δ z H T t y B₀ B₁ B₂ B₃ q : ℝ}
    (hθ : π / 2 < θ ∧ θ < π) (hη : 0 ≤ η) (hσ₀ : 1 / 2 < σ₀) (hσ : σ₀ ≤ σ)
    (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1) (hT : 2 ≤ T) (hTt : T ≤ t) (ht : 10 ≤ t)
    (hH : 4 ≤ H) (hz : z ≤ 0) (hy : 0 < y) (hzy : -z * kadiriSupport θ ≤ y)
    (hend : Real.exp y ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / (345 / 100))
    (hB₀ : kadiriDerivativeMoment θ 0 ≤ B₀) (hB₁ : kadiriDerivativeMoment θ 1 ≤ B₁)
    (hB₂ : kadiriDerivativeMoment θ 2 ≤ B₂) (hB₃ : kadiriDerivativeMoment θ 3 ≤ B₃)
    (S : Finset ℕ) (h₀ : 0 ∈ S) (a : ℕ → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i)
    (hq : η * Real.log t ≤ q) :
    kadiriBootstrapCorrection θ η η₀ σ₀ σ κ δ z H t S a ≤
      kadiriMomentCorrectionPolynomial θ η η₀ σ₀ κ δ z H T B₀ B₁ B₂ B₃ q S a := by
  have hTpos : 0 < T := by linarith
  have htpos : 0 < t := hTpos.trans_le hTt
  have hHpos : 0 < H := by linarith
  apply kadiriBootstrapCorrection_le_polynomial hθ hη hσ₀ hκ ht hHpos S a ha
    (kadiriDerivativeMass_le_momentMassBound hθ hz hy hzy hend hB₀ hB₁ hB₂ hB₃)
    (antitoneOn_kadiriPoleCoefficient S a ha hTpos htpos hTt)
  · simpa only [add_comm] using sum_xiLehmanTailMajorant_le_affine hT hTt hH S h₀ a ha
  · exact (antitoneOn_kadiriGammaResidual hκ hκ₁ σ S a ha hTpos htpos hTt).trans
      (antitoneOn_kadiriGammaResidual_sigma hκ T S a ha
        (by linarith : -2 < σ₀) (by linarith : -2 < σ) hσ)
  · exact kadiriTailLogCoefficient_nonneg hTpos hHpos S a ha
  · exact hq

end

end PrimeFactorUnimodality
