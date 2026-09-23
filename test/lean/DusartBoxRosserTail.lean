import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserBudget

/-! # Full box-tail consumers: arbitrary region constants and the proved initial region -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real intervalIntegral

example (m : ℕ) {h x R : ℝ} (hh : 0 < h) (hx : 1 < x) (hR : 0 < R)
    {s : ℂ} (hγ : 1 < |s.im|) (hβ0 : 0 ≤ s.re)
    (hβ : s.re ≤ 1 - 1 / (R * Real.log |s.im|)) :
    ‖iteratedBoxAverageComplex h (m + 3) (fun t => (t : ℂ) ^ s / s) x‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        logDampedPower (Real.log x / R) (m + 4 : ℕ) |s.im| :=
  norm_dusartBox_atom_le_abs_rosser_kernel m hh hx hR hγ hβ0 hβ

example (m : ℕ) {h x R T : ℝ} (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hT : 10 < T)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ p : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue p).im| →
      (riemannXiDivisorZeroValue p).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue p).im|)) :
    ‖dusartBoxXiHighSum m h x T‖ ≤ dusartBoxRosserTailBudget m h x R T :=
  norm_dusartBoxXiHighSum_le_rosserTail m hh hx hR hT hpeak hreg

example (m : ℕ) {h x T : ℝ} (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T)
    (hpeak : exp (sqrt ((Real.log x / 56) / (m + 4 : ℕ))) ≤ T) :
    ‖dusartBoxXiHighSum m h x T‖ ≤ dusartBoxRosserTailBudget m h x 56 T :=
  norm_dusartBoxXiHighSum_le_initialRosserTail m hh hx hT hpeak

example {h x T : ℝ} (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T)
    (hpeak : exp (sqrt ((Real.log x / 56) / (4 : ℕ))) ≤ T) :
    ‖dusartBoxXiHighSum 0 h x T‖ ≤ dusartBoxRosserTailBudget 0 h x 56 T :=
  norm_dusartBoxXiHighSum_le_initialRosserTail 0 hh hx hT hpeak

example (m : ℕ) {h x R a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ p : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue p).im| →
      (riemannXiDivisorZeroValue p).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue p).im|)) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxRosserErrorBudget m h x R a H T δ :=
  abs_dusartPsiAverageError_le_rosserBudget m hh hx hR ha haH hH hHT hδ hgap hpeak hreg

example (m : ℕ) {h x R a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (hR : 0 < R)
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hgap : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ p : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue p).im| →
      (riemannXiDivisorZeroValue p).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue p).im|)) :
    |ψ x - x| ≤
      max (dusartBoxRosserErrorBudget m h (x - (m + 3 : ℕ) * h) R a H T δ)
        (dusartBoxRosserErrorBudget m h x R a H T δ) + (m + 3 : ℕ) * h / 2 :=
  abs_psi_sub_le_dusartBoxRosserBudget m hh hx hR ha haH hH hHT hδ hgap hpeak hreg

end PrimeFactorUnimodality.Tests
