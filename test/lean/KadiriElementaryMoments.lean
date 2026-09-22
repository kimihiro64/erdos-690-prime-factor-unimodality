import PrimeFactorUnimodality.Helpers.Analytic.KadiriElementaryMoments

/-! # Full-support derivative moment regressions

Check the arbitrary-degree bound and the exact formulas for the four
moments used by the bootstrap. No sampled derivative values are used.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real

example {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (n : ℕ) :
    kadiriDerivativeMoment θ n ≤
      (-kadiriKernel₂ θ 0) * kadiriSupport θ ^ (n + 1) / (n + 1) :=
  kadiriDerivativeMoment_le_elementary hθ n

example {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (n : ℕ) :
    0 ≤ kadiriDerivativeMomentElementary θ n :=
  kadiriDerivativeMomentElementary_nonneg hθ n

example (θ : ℝ) : kadiriDerivativeMomentElementary θ 0 =
    (-kadiriKernel₂ θ 0) * kadiriSupport θ := by
  simp [kadiriDerivativeMomentElementary]

example (θ : ℝ) : kadiriDerivativeMomentElementary θ 1 =
    (-kadiriKernel₂ θ 0) * kadiriSupport θ ^ 2 / 2 := by
  norm_num [kadiriDerivativeMomentElementary]

example (θ : ℝ) : kadiriDerivativeMomentElementary θ 2 =
    (-kadiriKernel₂ θ 0) * kadiriSupport θ ^ 3 / 3 := by
  norm_num [kadiriDerivativeMomentElementary]

example (θ : ℝ) : kadiriDerivativeMomentElementary θ 3 =
    (-kadiriKernel₂ θ 0) * kadiriSupport θ ^ 4 / 4 := by
  norm_num [kadiriDerivativeMomentElementary]

end

end PrimeFactorUnimodality.Tests
