import PrimeFactorUnimodality.Helpers.Analytic.KadiriGammaBudget

/-! # One-sided real Gamma regressions

Exercise the entire positive real axis, the origin of the shifted factor,
zero shift, zero and unit subtraction coefficients, the strict improvement
in the zero harmonic, and the exact propagation into the Gamma residual.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Real

example {x : ℝ} (hx : 0 < x) : (digamma (x : ℂ)).re ≤ Real.log x :=
  re_digamma_ofReal_le_log hx

example : (digamma (1 : ℂ)).re ≤ 0 := by
  simpa using re_digamma_ofReal_le_log (x := 1) (by norm_num)

example : (digamma (1 / 2 : ℂ)).re ≤ Real.log (1 / 2) := by
  simpa using re_digamma_ofReal_le_log (x := 1 / 2) (by norm_num)

example {κ δ σ : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hσ : 0 ≤ σ) :
    smoothedGammaFactorDifference κ δ (σ : ℂ) ≤
      (1 - κ) / 2 * (Real.log (σ / 2 + 1) - Real.log π) + κ / (σ + 2) :=
  smoothedGammaFactorDifference_ofReal_le hκ hδ hσ

example {κ δ : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) :
    smoothedGammaFactorDifference κ δ 0 ≤ -(1 - κ) / 2 * Real.log π + κ / 2 := by
  convert! smoothedGammaFactorDifference_ofReal_le hκ hδ (σ := 0) (by norm_num) using 1
  simp
  ring

example {δ σ : ℝ} (hδ : 0 ≤ δ) (hσ : 0 ≤ σ) :
    smoothedGammaFactorDifference 0 δ (σ : ℂ) ≤
      (Real.log (σ / 2 + 1) - Real.log π) / 2 := by
  convert! smoothedGammaFactorDifference_ofReal_le (κ := 0) (by norm_num) hδ hσ using 1
  ring

example {δ σ : ℝ} (hδ : 0 ≤ δ) (hσ : 0 ≤ σ) :
    smoothedGammaFactorDifference 1 δ (σ : ℂ) ≤ 1 / (σ + 2) := by
  simpa using smoothedGammaFactorDifference_ofReal_le (κ := 1) (by norm_num) hδ hσ

example {κ σ : ℝ} (hκ : 0 ≤ κ) (hσ : 0 ≤ σ) :
    smoothedGammaFactorDifference κ 0 (σ : ℂ) ≤
      (1 - κ) / 2 * (Real.log (σ / 2 + 1) - Real.log π) + κ / (σ + 2) :=
  smoothedGammaFactorDifference_ofReal_le hκ (by norm_num) hσ

example (κ σ : ℝ) (hσ : -2 < σ) :
    smoothedGammaFactorError κ σ 0 < (1 + κ) / (σ + 2) := by
  rw [smoothedGammaFactorError_zero]
  exact (div_lt_div_iff_of_pos_right (by linarith : 0 < σ + 2)).mpr (by linarith)

example (σ : ℝ) : smoothedGammaFactorError 0 σ 0 = 0 := by simp

example (κ σ t : ℝ) (a : ℕ → ℝ) :
    kadiriGammaResidual κ σ t {0} a =
      (1 - κ) / 2 * (a 0 * (Real.log 2 - Real.log π)) + a 0 * (κ / (σ + 2)) := by
  simp [kadiriGammaResidual]

example {κ σ τ : ℝ} (hκ : 0 ≤ κ) (hσ : -2 < σ) (hστ : σ ≤ τ) :
    smoothedGammaFactorError κ τ 0 ≤ smoothedGammaFactorError κ σ 0 :=
  antitoneOn_smoothedGammaFactorError_sigma hκ 0 hσ (hσ.trans_le hστ) hστ

end

end PrimeFactorUnimodality.Tests
