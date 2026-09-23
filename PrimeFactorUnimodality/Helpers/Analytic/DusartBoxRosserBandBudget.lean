import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPsiError
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserClosedTail
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserIncreasingBand
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxTwoCutoffs

/-! # The actual psi error with Rosser damping in both the band and tail

The finite band keeps the height inside the damping factor and uses the
increasing exponent-one estimate. The infinite tail uses the full `m+4`
power and the closed majorant. One arbitrary region constant controls both
blocks. The low-height gap remains an explicit mathematical input.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

/-- The finite prefix, increasing band, decreasing tail, and all analytic corrections. -/
def dusartBoxRosserBandErrorBudget (m : ℕ) (h x R p a H T δ : ℝ) : ℝ :=
  ((x + (m + 3 : ℕ) * h) * exp (-δ * Real.log x)) * xiLowReciprocalNormBound a H δ +
    (x + (m + 3 : ℕ) * h) * xiRosserIncreasingBandBound (Real.log x / R) H T +
    dusartBoxRosserClosedTailBudget m h x R p T +
    1 / (2 * (x ^ 2 - 1)) + Real.log (2 * π)

/-- The actual average satisfies the complete elementary two-kernel estimate. -/
theorem abs_dusartPsiAverageError_le_rosserBandBudget (m : ℕ) {h x R p a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hinc : T ≤ exp (sqrt (Real.log x / R)))
    (hdec : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxRosserBandErrorBudget m h x R p a H T δ := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlo := (norm_sum_dusartBox_xi_power_average_le m hh hx hδ.le
    (xiLowHeightIndices H) hgap).trans (mul_le_mul_of_nonneg_left
      (sum_xi_low_reciprocal_norm_le_explicit ha haH hδ hgap) (by positivity))
  have hmid := norm_dusartBox_band_le_rosser_increasing m hh hx hR hH hHT hinc
    (fun z hz => hreg z ((mem_xiHeightBandIndices H T z).mp hz).1)
  have hhi := norm_dusartBoxXiHighSum_le_rosserClosedTail m hh hx hR hp hpq
    (by linarith) hdec (fun z hz => hreg z (hHT.trans hz))
  have hs := (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hlo hmid)) hhi)
  rw [← smoothedXiPairedSum_box_eq_low_add_band_add_high m hh hx hHT] at hs
  exact (abs_dusartPsiAverageError_le_zero_sum m hh hx).trans
    (add_le_add (add_le_add hs le_rfl) le_rfl)

/-- Adjacent averages preserve the increasing-band and decreasing-tail conditions. -/
theorem abs_psi_sub_le_dusartBoxRosserBandBudget (m : ℕ) {h x R p a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hinc : T ≤ exp (sqrt (Real.log (x - (m + 3 : ℕ) * h) / R)))
    (hdec : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| ≤
      max (dusartBoxRosserBandErrorBudget m h (x - (m + 3 : ℕ) * h) R p a H T δ)
        (dusartBoxRosserBandErrorBudget m h x R p a H T δ) + (m + 3 : ℕ) * h / 2 := by
  have hleft : x - (m + 3 : ℕ) * h ≤ x :=
    sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hh.le)
  have hx' : 1 < x := hx.trans_le hleft
  have hlog := div_le_div_of_nonneg_right
    (Real.log_le_log (lt_trans zero_lt_one hx) hleft) hR.le
  have hinc' := hinc.trans (Real.exp_le_exp.mpr (Real.sqrt_le_sqrt hlog))
  have hdec' : exp (sqrt ((Real.log (x - (m + 3 : ℕ) * h) / R) / (m + 4 : ℕ))) ≤ T :=
    (Real.exp_le_exp.mpr (Real.sqrt_le_sqrt
      (div_le_div_of_nonneg_right hlog (Nat.cast_nonneg _)))).trans hdec
  exact dusart_abs_psi_error_le_of_averages (m + 3) hh
    ((abs_dusartPsiAverageError_le_rosserBandBudget m hh hx hR hp hpq
      ha haH hH hHT hδ hgap hinc hdec' hreg).trans (le_max_left _ _))
    ((abs_dusartPsiAverageError_le_rosserBandBudget m hh hx' hR hp hpq
      ha haH hH hHT hδ hgap hinc' hdec hreg).trans (le_max_right _ _))

end

end PrimeFactorUnimodality
