import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserBudget
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserClosedTail

/-! # The actual pointwise psi error bounded entirely by elementary functions

Replace the convergent high-tail integrals by the proved closed majorant
while keeping the finite blocks and every correction unchanged. The power
parameter is arbitrary in `1<p<m+4`, ready for uniform scalar optimization.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

/-- A complete elementary budget for the averaged psi error. -/
def dusartBoxRosserClosedErrorBudget (m : ℕ) (h x R p a H T δ : ℝ) : ℝ :=
  dusartBoxLowBandBudget m h x a H T δ + dusartBoxRosserClosedTailBudget m h x R p T +
    1 / (2 * (x ^ 2 - 1)) + Real.log (2 * Real.pi)

/-- Replacing only the high-tail term preserves the full integral estimate. -/
theorem dusartBoxRosserErrorBudget_le_closed (m : ℕ) {h x R p a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hp : 1 < p)
    (hpq : p < (m + 4 : ℕ)) (hT : 10 < T) :
    dusartBoxRosserErrorBudget m h x R a H T δ ≤
      dusartBoxRosserClosedErrorBudget m h x R p a H T δ :=
  add_le_add (add_le_add (add_le_add le_rfl
    (dusartBoxRosserTailBudget_le_closed m hh hx hR hp hpq hT)) le_rfl) le_rfl

/-- The averaged psi error has the closed scalar majorant, with no zero sum or integral. -/
theorem abs_dusartPsiAverageError_le_rosserClosedBudget (m : ℕ) {h x R p a H T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hR : 0 < R) (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hpeak : exp (sqrt ((Real.log x / R) / (m + 4 : ℕ))) ≤ T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxRosserClosedErrorBudget m h x R p a H T δ :=
  (abs_dusartPsiAverageError_le_rosserBudget m hh hx hR ha haH hH hHT hδ hgap hpeak hreg).trans
    (dusartBoxRosserErrorBudget_le_closed m hh hx hR hp hpq (by linarith))

/-- The complete pointwise estimate now contains only elementary scalar functions. -/
theorem abs_psi_sub_le_dusartBoxRosserClosedBudget (m : ℕ) {h x R p a H T δ : ℝ}
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
        (dusartBoxRosserClosedErrorBudget m h x R p a H T δ) + (m + 3 : ℕ) * h / 2 := by
  have hx' : 1 < x := by
    have hn := mul_nonneg (Nat.cast_nonneg (m + 3) (α := ℝ)) hh.le
    linarith
  have hT : 10 < T := by linarith
  exact (abs_psi_sub_le_dusartBoxRosserBudget m hh hx hR ha haH hH hHT hδ hgap hpeak hreg).trans
    (add_le_add (max_le_max
      (dusartBoxRosserErrorBudget_le_closed m hh hx hR hp hpq hT)
      (dusartBoxRosserErrorBudget_le_closed m hh hx' hR hp hpq hT)) le_rfl)

end

end PrimeFactorUnimodality
