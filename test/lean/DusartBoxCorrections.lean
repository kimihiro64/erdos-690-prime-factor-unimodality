import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPsiError

/-! # Negative-even correction and endpoint regressions

The first pole and every later pole are included. The complete geometric
majorant is tested at a concrete endpoint, and the actual averaged error
retains the full xi sum and the nonzero endpoint constant.
-/

namespace PrimeFactorUnimodality.Tests

open Complex intervalIntegral

example {x t : ℝ} (hx : 1 < x) (ht : x ≤ t) (n : ℕ) :
    ‖(t : ℂ) ^ shiftedGammaPole n / shiftedGammaPole n‖ ≤
      ((x ^ 2)⁻¹) ^ (n + 1) / 2 := norm_dusartBox_gamma_power_le hx ht n

example {t : ℝ} (ht : 2 ≤ t) : ‖(t : ℂ) ^ (-2 : ℂ) / (-2)‖ ≤ 1 / 8 := by
  have he := norm_dusartBox_gamma_power_le (by norm_num : (1 : ℝ) < 2) ht 0
  norm_num [shiftedGammaPole] at he ⊢
  exact he

example (m n : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    ‖iteratedBoxAverageComplex h (m + 3)
      (fun t => (t : ℂ) ^ shiftedGammaPole n / shiftedGammaPole n) x‖ ≤
        ((x ^ 2)⁻¹) ^ (n + 1) / 2 := norm_dusartBox_gamma_average_le m hh hx n

example {x : ℝ} (hx : 1 < x) :
    HasSum (fun n : ℕ => ((x ^ 2)⁻¹) ^ (n + 1) / 2) (1 / (2 * (x ^ 2 - 1))) :=
  hasSum_dusartBox_gamma_majorant hx

example : HasSum (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1) / 2) (1 / 6) := by
  convert hasSum_dusartBox_gamma_majorant (by norm_num : (1 : ℝ) < 2) using 1 <;> norm_num

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    smoothedGammaPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
      (dusartBoxSupport m h x) 0 =
      ∑' n : ℕ, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ shiftedGammaPole n / shiftedGammaPole n) x :=
  smoothedGammaPairedSum_box_eq_power_average m hh hx

example {h : ℝ} (hh : 0 < h) :
    ‖smoothedGammaPairedSum (fun u => (dusartBoxWeight 0 h 2 u : ℂ))
      (dusartBoxSupport 0 h 2) 0‖ ≤ 1 / 6 := by
  convert norm_smoothedGammaPairedSum_box_le 0 hh (by norm_num : (1 : ℝ) < 2) using 1
  norm_num

example : logDeriv riemannXi 0 +
    ((Real.log Real.pi : ℂ) + Real.eulerMascheroniConstant) / 2 + 1 =
      (Real.log (2 * Real.pi) : ℂ) := dusartBox_endpoint_constant

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    (dusartPsiAverageError (m + 3) h x : ℂ) =
      -smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
        (dusartBoxSupport m h x) 0 -
      smoothedGammaPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
        (dusartBoxSupport m h x) 0 - (Real.log (2 * Real.pi) : ℂ) :=
  dusartPsiAverageError_eq_normalized_spectral m hh hx

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    |dusartPsiAverageError (m + 3) h x| ≤
      ‖smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
        (dusartBoxSupport m h x) 0‖ + 1 / (2 * (x ^ 2 - 1)) + Real.log (2 * Real.pi) :=
  abs_dusartPsiAverageError_le_zero_sum m hh hx

end PrimeFactorUnimodality.Tests
