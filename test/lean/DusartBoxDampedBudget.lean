import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxDampedBudget

/-! # Explicit damped-tail, pointwise-error, and fixed-target regressions -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev

example {x T B : ℝ} (hx : 1 ≤ x) (hT : 10 ^ 9 ≤ T)
    (p : RiemannXiDivisorZeroIndex) (hp : T ≤ |(riemannXiDivisorZeroValue p).im|)
    (hb : |(riemannXiDivisorZeroValue p).im| ≤ B) :
    xiInitialDampedHeightKernel x p ≤
      Real.exp (-(1 / (56 * Real.log B)) * Real.log x) *
        (1 / (riemannXiDivisorZeroValue p).im ^ 2) :=
  xiInitialDampedHeightKernel_le_cutoff hx hT p hp hb

example {x T B : ℝ} (hx : 1 ≤ x) (hT : 10 ^ 9 ≤ T) (hTB : T ≤ B) :
    xiInitialDampedHeightTail x T ≤
      Real.exp (-(1 / (56 * Real.log B)) * Real.log x) * xiHeightTail 0 T +
        xiHeightTail 0 B := xiInitialDampedHeightTail_le_split hx hT hTB

example {x T B : ℝ} (hx : 1 ≤ x) (hT : 10 ^ 9 ≤ T) (hTB : T ≤ B) :
    xiInitialDampedHeightTail x T ≤
      Real.exp (-(1 / (56 * Real.log B)) * Real.log x) *
        (4 * xiLehmanHighBound (T / 2) (T / 2)) + 4 * xiLehmanHighBound (B / 2) (B / 2) :=
  xiInitialDampedHeightTail_le_split_highBound hx hT hTB

example (m : ℕ) {h x T B : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T) (hTB : T ≤ B) :
    ‖dusartBoxXiHighSum m h x T‖ ≤ dusartBoxTailFactor m h x T *
      dusartBoxDampedTailBudget x T B := norm_dusartBoxXiHighSum_le_dampedBudget m hh hx hT hTB

example (m : ℕ) {h x a H T B δ : ℝ} (hh : 0 < h) (hx : 1 < x) (hT : 0 < T) :
    dusartBoxDampedErrorBudget m h x a H T B δ ≤
      dusartBoxTwoCutoffErrorBudget m h x a H T δ :=
  dusartBoxDampedErrorBudget_le_twoCutoff m hh hx hT

example (m : ℕ) {h x a H T B δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hTB : T ≤ B) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxDampedErrorBudget m h x a H T B δ :=
  abs_dusartPsiAverageError_le_dampedBudget m hh hx ha haH hH hHT hTB hδ hg

example (m : ℕ) {h x a H T B δ : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hTB : T ≤ B) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    |ψ x - x| ≤
      max (dusartBoxDampedErrorBudget m h (x - (m + 3 : ℕ) * h) a H T B δ)
        (dusartBoxDampedErrorBudget m h x a H T B δ) + (m + 3 : ℕ) * h / 2 :=
  abs_psi_sub_le_dusartBoxDampedBudget m hh hx ha haH hH hHT hTB hδ hg

example {A X H δ : ℝ} (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (h : HasDusartDampedScalarBudget A X H δ) : HasPsiLogFourthError A X :=
  hasPsiLogFourthError_of_dampedBudget hH hδ hg h

example {H δ : ℝ} (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    (h : HasDusartDampedScalarBudget (1 / 2) (4e18) H δ) :
    ∀ x : ℝ, 4e18 ≤ x → |θ x - x| ≤ (648 / 1000) * x / (Real.log x) ^ 4 :=
  hasThetaLogFourthError_648_of_dampedBudget hH hδ hg h

end PrimeFactorUnimodality.Tests
