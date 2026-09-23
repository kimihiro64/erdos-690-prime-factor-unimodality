import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserTail
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxTwoCutoffBudget

/-! # The Rosser high-tail integral in the actual pointwise psi estimate

Combine the new complete tail with the already proved finite low/band
bounds and correction terms. Adjacent averages then control the actual
pointwise Chebyshev error, including its exact smoothing loss. The region
constant stays arbitrary; low-height and numerical integral inputs remain explicit.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

/-- All spectral blocks and corrections, with the convergent Rosser integral for the high block. -/
def dusartBoxRosserErrorBudget (m : ℕ) (h x R a H T δ : ℝ) : ℝ :=
  dusartBoxLowBandBudget m h x a H T δ + dusartBoxRosserTailBudget m h x R T +
    1 / (2 * (x ^ 2 - 1)) + Real.log (2 * Real.pi)

/-- The Rosser integral estimate is connected to the actual averaged psi error. -/
theorem abs_dusartPsiAverageError_le_rosserBudget (m : ℕ) {h x R a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ p : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue p).im| →
      (riemannXiDivisorZeroValue p).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue p).im|)) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxRosserErrorBudget m h x R a H T δ := by
  have he : ‖smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
      (dusartBoxSupport m h x) 0‖ ≤
      dusartBoxLowBandBudget m h x a H T δ + dusartBoxRosserTailBudget m h x R T := by
    rw [smoothedXiPairedSum_box_eq_low_add_band_add_high m hh hx hHT]
    exact (norm_add_le _ _).trans (add_le_add
      (norm_dusartBox_low_add_band_le m hh hx ha haH hH hHT hδ hgap)
      (norm_dusartBoxXiHighSum_le_rosserTail m hh hx hR (by linarith) hpeak hreg))
  exact (abs_dusartPsiAverageError_le_zero_sum m hh hx).trans
    (add_le_add (add_le_add he le_rfl) le_rfl)

/-- The upper evaluation point's turning-height condition also controls the lower average. -/
theorem abs_psi_sub_le_dusartBoxRosserBudget (m : ℕ) {h x R a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (hR : 0 < R)
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ p : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue p).im| →
      (riemannXiDivisorZeroValue p).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue p).im|)) :
    |ψ x - x| ≤
      max (dusartBoxRosserErrorBudget m h (x - (m + 3 : ℕ) * h) R a H T δ)
        (dusartBoxRosserErrorBudget m h x R a H T δ) + (m + 3 : ℕ) * h / 2 := by
  have hleft : x - (m + 3 : ℕ) * h ≤ x :=
    sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hh.le)
  have hx' : 1 < x := hx.trans_le hleft
  have hlog := Real.log_le_log (lt_trans zero_lt_one hx) hleft
  have hpeak' : exp (sqrt ((Real.log (x - (m + 3 : ℕ) * h) / R) / (m + 4 : ℕ))) ≤ T :=
    (Real.exp_le_exp.mpr (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right hlog hR.le) (Nat.cast_nonneg _)))).trans hpeak
  exact dusart_abs_psi_error_le_of_averages (m + 3) hh
    ((abs_dusartPsiAverageError_le_rosserBudget m hh hx hR ha haH hH hHT hδ hgap hpeak' hreg).trans
      (le_max_left _ _))
    ((abs_dusartPsiAverageError_le_rosserBudget m hh hx' hR ha haH hH hHT hδ hgap hpeak hreg).trans
      (le_max_right _ _))

end

end PrimeFactorUnimodality
