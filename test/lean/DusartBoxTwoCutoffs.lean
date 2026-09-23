import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxTwoCutoffBudget

/-! # Actual two-cutoff estimates and their fixed-low-input provider boundary -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev intervalIntegral

example (m : ℕ) {h x H T : ℝ} (hh : 0 < h) (hx : 1 < x) (hHT : H ≤ T) :
    smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) 0 =
      (∑ p ∈ xiLowHeightIndices H, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x) +
      (∑ p ∈ xiHeightBandIndices H T, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x) +
        dusartBoxXiHighSum m h x T :=
  smoothedXiPairedSum_box_eq_low_add_band_add_high m hh hx hHT

example (m : ℕ) {h x a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    ‖smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
        (dusartBoxSupport m h x) 0‖ ≤ dusartBoxTwoCutoffZeroBudget m h x a H T δ :=
  norm_smoothedXiPairedSum_box_le_two_cutoffs m hh hx ha haH hH hHT hδ hg

example (m : ℕ) {h x a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxTwoCutoffErrorBudget m h x a H T δ :=
  abs_dusartPsiAverageError_le_twoCutoffBudget m hh hx ha haH hH hHT hδ hg

example (m : ℕ) (h x a H δ : ℝ) :
    dusartBoxTwoCutoffErrorBudget m h x a H H δ =
      dusartBoxCountingErrorBudget m h x a H δ := by simp

example (m : ℕ) {h x a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    |ψ x - x| ≤
      max (dusartBoxTwoCutoffErrorBudget m h (x - (m + 3 : ℕ) * h) a H T δ)
        (dusartBoxTwoCutoffErrorBudget m h x a H T δ) + (m + 3 : ℕ) * h / 2 :=
  abs_psi_sub_le_dusartBoxTwoCutoffBudget m hh hx ha haH hH hHT hδ hg

example {A X H δ : ℝ} (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (h : HasDusartTwoCutoffScalarBudget A X H δ) : HasPsiLogFourthError A X :=
  hasPsiLogFourthError_of_twoCutoffBudget hH hδ hg h

example {H δ : ℝ} (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (h : HasDusartTwoCutoffScalarBudget (1 / 2) (4e18) H δ) :
    ∀ x : ℝ, 4e18 ≤ x → |θ x - x| ≤ (648 / 1000) * x / (Real.log x) ^ 4 :=
  hasThetaLogFourthError_648_of_twoCutoffBudget hH hδ hg h

end PrimeFactorUnimodality.Tests
