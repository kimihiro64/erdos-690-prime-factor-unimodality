import PrimeFactorUnimodality.Helpers.Analytic.KadiriExplicitMaster

/-! # Height-decaying Gamma error regressions

Check finite and limiting reciprocal errors, the zero truncation, signed
heights, the improved zero-height error, the minimum with the previous bound,
and monotonicity at arbitrary natural harmonics.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Real

example {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    ‖(∑ k ∈ Finset.range (N + 1), (z + (k : ℂ))⁻¹) -
      (Complex.log (z + N) - Complex.log z)‖ ≤ 2 / ‖z‖ :=
  norm_sum_inv_add_sub_log_le_inv_norm hz N

example {z : ℂ} (hz : 0 < z.re) : ‖z⁻¹‖ ≤ 2 / ‖z‖ := by
  simpa using norm_sum_inv_add_sub_log_le_inv_norm hz 0

example {z : ℂ} (hz : 0 < z.re) :
    ‖digamma z - Complex.log z‖ ≤ min (1 / z.re) (2 / ‖z‖) :=
  le_min (norm_digamma_sub_log_le_inv_re hz) (norm_digamma_sub_log_le_inv_norm hz)

example (t : ℝ) :
    ‖digamma (1 + (t : ℂ) * I) - Complex.log (1 + (t : ℂ) * I)‖ ≤
      2 / ‖1 + (t : ℂ) * I‖ :=
  norm_digamma_sub_log_le_inv_norm (by simp)

example {κ δ : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) {s : ℂ} (hs : 0 ≤ s.re) :
    smoothedGammaFactorDifference κ δ s ≤
      (1 - κ) / 2 * (Real.log ‖s / 2 + 1‖ - Real.log π) + (1 + κ) / ‖s / 2 + 1‖ :=
  smoothedGammaFactorDifference_le_log_norm_inv_norm hκ hδ hs

example {δ : ℝ} (hδ : 0 ≤ δ) {s : ℂ} (hs : 0 ≤ s.re) (ht : s.im ≠ 0) :
    smoothedGammaFactorDifference 1 δ s ≤ 4 / |s.im| := by
  convert! smoothedGammaFactorDifference_le_log_norm_height (κ := 1) (by norm_num) hδ hs ht using 1
  norm_num

example (κ σ : ℝ) : smoothedGammaFactorError κ σ 0 = κ / (σ + 2) :=
  smoothedGammaFactorError_zero κ σ

example (κ σ t : ℝ) (hσ : -2 ≤ σ) :
    smoothedGammaFactorError κ σ t ≤ (1 + κ) / (σ + 2) :=
  smoothedGammaFactorError_le_re κ σ t hσ

example (κ σ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    smoothedGammaFactorError κ σ t ≤ 2 * (1 + κ) / |t| :=
  smoothedGammaFactorError_le_height κ σ ht

example (κ σ t : ℝ) : smoothedGammaFactorError κ σ (-t) =
    smoothedGammaFactorError κ σ t := by simp [smoothedGammaFactorError]

example (κ σ t : ℝ) (hσ : -2 ≤ σ) : smoothedGammaFactorMajorant κ σ t ≤
    (1 - κ) / 2 * (Real.log (|t| / 2 + 2) - Real.log π) + (1 + κ) / (σ + 2) :=
  add_le_add le_rfl (smoothedGammaFactorError_le_re κ σ t hσ)

example {κ T t : ℝ} (hκ : 0 ≤ κ) (σ : ℝ) (i : ℕ) (hT : 0 < T) (hTt : T ≤ t) :
    smoothedGammaFactorError κ σ ((i : ℝ) * t) ≤
      smoothedGammaFactorError κ σ ((i : ℝ) * T) :=
  antitoneOn_smoothedGammaFactorError_nat hκ σ i hT (hT.trans_le hTt) hTt

end

end PrimeFactorUnimodality.Tests
