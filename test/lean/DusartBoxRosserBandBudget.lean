import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserBandBudget

/-! # Actual box bands and the full two-kernel pointwise psi estimate -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Complex Real intervalIntegral

example (m : ℕ) {h x R : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) {s : ℂ} (hγ : 1 < |s.im|)
    (hβ : s.re ≤ 1 - 1 / (R * Real.log |s.im|)) :
    ‖iteratedBoxAverageComplex h (m + 3) (fun t => (t : ℂ) ^ s / s) x‖ ≤
      (x + (m + 3 : ℕ) * h) * logDampedPower (Real.log x / R) 1 |s.im| :=
  norm_dusartBox_atom_le_rosser_one m hh hx hR hγ hβ

example (m : ℕ) {h x R H T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hH : 20 ≤ H) (hHT : H ≤ T)
    (hT : T ≤ exp (sqrt (Real.log x / R)))
    (hreg : ∀ p ∈ xiHeightBandIndices H T, (riemannXiDivisorZeroValue p).re ≤
      1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue p).im|)) :
    ‖∑ p ∈ xiHeightBandIndices H T, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x‖ ≤
      (x + (m + 3 : ℕ) * h) * xiRosserIncreasingBandBound (Real.log x / R) H T :=
  norm_dusartBox_band_le_rosser_increasing m hh hx hR hH hHT hT hreg

example (m : ℕ) {h x H T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T)
    (hT : T ≤ exp (sqrt (Real.log x / 56))) :
    ‖∑ p ∈ xiHeightBandIndices H T, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x‖ ≤
      (x + (m + 3 : ℕ) * h) * xiRosserIncreasingBandBound (Real.log x / 56) H T :=
  norm_dusartBox_band_le_initial_rosser_increasing m hh hx hH hHT hT

example (m : ℕ) (h x R H : ℝ) :
    ‖∑ p ∈ xiHeightBandIndices H H, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x‖ =
      (x + (m + 3 : ℕ) * h) * xiRosserIncreasingBandBound (Real.log x / R) H H := by simp

example (m : ℕ) {h x R p a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hH : 20 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hinc : T ≤ exp (sqrt (Real.log x / R)))
    (hdec : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxRosserBandErrorBudget m h x R p a H T δ :=
  abs_dusartPsiAverageError_le_rosserBandBudget m hh hx hR hp hpq
    ha haH hH hHT hδ hgap hinc hdec hreg

-- The increasing condition is imposed at the lower average; the decreasing one at the upper.
example (m : ℕ) {h x R p a H T δ : ℝ}
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
        (dusartBoxRosserBandErrorBudget m h x R p a H T δ) + (m + 3 : ℕ) * h / 2 :=
  abs_psi_sub_le_dusartBoxRosserBandBudget m hh hx hR hp hpq
    ha haH hH hHT hδ hgap hinc hdec hreg

end PrimeFactorUnimodality.Tests
