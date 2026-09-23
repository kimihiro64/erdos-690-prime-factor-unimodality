import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxGammaBounds
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxSpectralFormula

/-! # The actual averaged psi error with all correction terms controlled

The exact xi constant from the pinned PNT dependency simplifies the
endpoint term to `log(2*pi)`. The negative-even bound controls the full
Gamma series. Thus estimating the complete xi sum suffices for a bound
on the actual averaged Chebyshev error; no correction term is discarded.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex intervalIntegral

/-- Simplify the constant using the proved exact logarithmic derivative of xi. -/
theorem dusartBox_endpoint_constant :
    logDeriv riemannXi 0 +
      ((Real.log Real.pi : ℂ) + Real.eulerMascheroniConstant) / 2 + 1 =
        (Real.log (2 * Real.pi) : ℂ) := by
  have hlog : Real.log (4 * Real.pi) + Real.log Real.pi =
      2 * Real.log (2 * Real.pi) := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne',
      Real.log_mul (by norm_num) Real.pi_pos.ne']
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [h4]
    ring
  have hc := congrArg Complex.ofReal hlog
  push_cast at hc
  linear_combination (-1 / 2 : ℂ) * neg_two_mul_logDeriv_riemannXi_zero_eq +
    (1 / 2 : ℂ) * hc

/-- The normalized explicit formula for the actual average, including both zero families. -/
theorem dusartPsiAverageError_eq_normalized_spectral (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) :
    (dusartPsiAverageError (m + 3) h x : ℂ) =
      -smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
        (dusartBoxSupport m h x) 0 -
      smoothedGammaPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
        (dusartBoxSupport m h x) 0 - (Real.log (2 * Real.pi) : ℂ) := by
  rw [dusartPsiAverageError_eq_spectral m hh hx,
    ← smoothedXiPairedSum_box_eq_power_average m hh hx]
  linear_combination -dusartBox_endpoint_constant

/-- Only the actual xi series remains after the explicit correction budget. -/
theorem abs_dusartPsiAverageError_le_zero_sum (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) :
    |dusartPsiAverageError (m + 3) h x| ≤
      ‖smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
        (dusartBoxSupport m h x) 0‖ +
        1 / (2 * (x ^ 2 - 1)) + Real.log (2 * Real.pi) := by
  let X := smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
    (dusartBoxSupport m h x) 0
  let G := smoothedGammaPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
    (dusartBoxSupport m h x) 0
  have hlog : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hnorm := (norm_sub_le (-X - G) (Real.log (2 * Real.pi) : ℂ)).trans
    (add_le_add (norm_sub_le (-X) G) le_rfl)
  simp only [norm_neg, norm_real, Real.norm_eq_abs, abs_of_nonneg hlog] at hnorm
  rw [← Real.norm_eq_abs, ← Complex.norm_real,
    dusartPsiAverageError_eq_normalized_spectral m hh hx]
  exact hnorm.trans (add_le_add
    (add_le_add le_rfl (norm_smoothedGammaPairedSum_box_le m hh hx)) le_rfl)

end

end PrimeFactorUnimodality
