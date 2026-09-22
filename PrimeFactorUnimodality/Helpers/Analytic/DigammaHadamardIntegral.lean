import PrimeFactorUnimodality.Helpers.Analytic.DigammaHadamard
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Hadamard.Integral

/-! # Absolute integration of the shifted digamma pole series

The negative even poles have a summable three-halves moment. Absolute
Hadamard interchange therefore applies to any quadratic contour weight.
When its integral is zero, the Euler constant cancels, leaving precisely
minus twice the sum of the integrated regularized pole atoms.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory

/-- The complete digamma contour integrand is absolutely integrable. -/
theorem integrable_mul_digamma_half_add_one
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) {H : ℝ → ℂ} (hH : Integrable H)
    (hBound : ∀ t, ‖H t‖ ≤ C / ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2) :
    Integrable (fun t : ℝ => H t * digamma (((c : ℂ) + (t : ℂ) * I) / 2 + 1)) := by
  have hA := integrable_mul_tsum_hadamardAtoms hc hc hC
    shiftedGammaPole_ne_zero shiftedGammaPole_re_nonpos
    summable_shiftedGammaPole_norm_inv_rpow hH hBound
  apply ((hH.mul_const (-(Real.eulerMascheroniConstant : ℂ))).sub
    (hA.const_mul 2)).congr
  filter_upwards with t
  rw [digamma_half_add_one_eq_shiftedGamma_tsum (by simpa using hc)]
  simp only [Pi.sub_apply]
  ring

/-- The zero-mass weight cancels Euler's constant and permits whole-series interchange. -/
theorem integral_mul_digamma_half_add_one_eq_tsum
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) {H : ℝ → ℂ} (hH : Integrable H)
    (hBound : ∀ t, ‖H t‖ ≤ C / ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2)
    (hZero : (∫ t : ℝ, H t) = 0) :
    (∫ t : ℝ, H t * digamma (((c : ℂ) + (t : ℂ) * I) / 2 + 1)) =
      -2 * ∑' n : ℕ, ∫ t : ℝ,
        H t * (1 / ((c : ℂ) + (t : ℂ) * I - shiftedGammaPole n) +
          1 / shiftedGammaPole n) := by
  let A : ℝ → ℂ := fun t => ∑' n : ℕ,
    (1 / ((c : ℂ) + (t : ℂ) * I - shiftedGammaPole n) + 1 / shiftedGammaPole n)
  have hA : Integrable (fun t => H t * A t) :=
    integrable_mul_tsum_hadamardAtoms hc hc hC
      shiftedGammaPole_ne_zero shiftedGammaPole_re_nonpos
      summable_shiftedGammaPole_norm_inv_rpow hH hBound
  have hswap := tsum_integral_mul_hadamardAtoms hc hc hC
    shiftedGammaPole_ne_zero shiftedGammaPole_re_nonpos
    summable_shiftedGammaPole_norm_inv_rpow hH hBound
  calc
    _ = ∫ t : ℝ, H t * (-(Real.eulerMascheroniConstant : ℂ)) - 2 * (H t * A t) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [digamma_half_add_one_eq_shiftedGamma_tsum (by simpa using hc)]
      dsimp [A]
      ring
    _ = -2 * (∫ t : ℝ, H t * A t) := by
      rw [integral_sub (hH.mul_const _) (hA.const_mul 2), integral_mul_const,
        hZero, zero_mul, integral_const_mul, zero_sub]
      ring
    _ = _ := congrArg (fun z : ℂ => -2 * z) hswap.symm

end

end PrimeFactorUnimodality
