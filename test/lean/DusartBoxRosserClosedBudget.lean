import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserClosedBudget

/-! # Closed Rosser bounds for the actual full tail and pointwise psi error -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real

example {a q p u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hp : 1 < p) (hpq : p < q) (hu : 10 < u) :
    xiRosserTailIntegral a q u ≤
      logDampedPowerMajorant a q p u * logDampedPowerIntegralFactor p (2 * π) u :=
  xiRosserTailIntegral_le_closed ha hq hp hpq hu

example {a q p u : ℝ}
    (ha : 0 ≤ a) (hq : 2 ≤ q) (hp : 1 < p) (hpq : p < q) (hu : 10 < u)
    (hw : exp (sqrt (a / q)) ≤ u) :
    xiRosserAbsoluteTail a q u ≤ xiRosserClosedTailBound a q p u :=
  xiRosserAbsoluteTail_le_closed ha hq hp hpq hu hw

example {a q p u : ℝ} (hp : 1 < p) (hu : 10 < u) :
    0 ≤ xiRosserClosedTailBound a q p u :=
  xiRosserClosedTailBound_nonneg hp hu

example {u : ℝ} (hu : 10 < u) :
    xiRosserAbsoluteTail 0 2 u ≤ xiRosserClosedTailBound 0 2 (3 / 2) u := by
  apply xiRosserAbsoluteTail_le_closed le_rfl le_rfl (by norm_num) (by norm_num) hu
  simpa using (show 1 ≤ u by linarith)

example (m : ℕ) {h x R p T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hp : 1 < p)
    (hpq : p < (m + 4 : ℕ)) (hT : 10 < T)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    ‖dusartBoxXiHighSum m h x T‖ ≤ dusartBoxRosserClosedTailBudget m h x R p T :=
  norm_dusartBoxXiHighSum_le_rosserClosedTail m hh hx hR hp hpq hT hpeak hreg

-- The initial-region specialization has no assumed zero-free region.
example (m : ℕ) {h x p T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (hT : 10 ^ 9 ≤ T) (hpeak : exp (sqrt ((Real.log x / 56) / (m + 4 : ℕ))) ≤ T) :
    ‖dusartBoxXiHighSum m h x T‖ ≤ dusartBoxRosserClosedTailBudget m h x 56 p T :=
  norm_dusartBoxXiHighSum_le_initialRosserClosedTail m hh hx hp hpq hT hpeak

example {h x T : ℝ} (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T)
    (hpeak : exp (sqrt ((Real.log x / 56) / (4 : ℕ))) ≤ T) :
    ‖dusartBoxXiHighSum 0 h x T‖ ≤ dusartBoxRosserClosedTailBudget 0 h x 56 2 T :=
  norm_dusartBoxXiHighSum_le_initialRosserClosedTail 0 hh hx
    (by norm_num) (by norm_num) hT hpeak

example (m : ℕ) {h x R p a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxRosserClosedErrorBudget m h x R p a H T δ :=
  abs_dusartPsiAverageError_le_rosserClosedBudget m hh hx hR hp hpq
    ha haH hH hHT hδ hgap hpeak hreg

example (m : ℕ) {h x R p a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (hR : 0 < R)
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |ψ x - x| ≤
      max (dusartBoxRosserClosedErrorBudget m h (x - (m + 3 : ℕ) * h) R p a H T δ)
        (dusartBoxRosserClosedErrorBudget m h x R p a H T δ) + (m + 3 : ℕ) * h / 2 :=
  abs_psi_sub_le_dusartBoxRosserClosedBudget m hh hx hR hp hpq
    ha haH hH hHT hδ hgap hpeak hreg

end PrimeFactorUnimodality.Tests
