import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxCountingBudget

/-! # Provider regressions with the reciprocal-norm mass discharged

These consumers have no independent mass hypothesis: only the stated
low-zero gap and scalar budget remain. The fixed target is not weakened.
-/

namespace PrimeFactorUnimodality.Tests

open Chebyshev

example (m : ℕ) {h x a T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (ha : 10 ≤ a) (haT : a < T) (hT : 10 ^ 9 ≤ T) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    |dusartPsiAverageError (m + 3) h x| ≤ dusartBoxCountingErrorBudget m h x a T δ :=
  abs_dusartPsiAverageError_le_countingBudget m hh hx ha haT hT hδ hg

example (m : ℕ) {h x a T δ : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (ha : 10 ≤ a) (haT : a < T)
    (hT : 10 ^ 9 ≤ T) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    |ψ x - x| ≤
      max (dusartBoxCountingErrorBudget m h (x - (m + 3 : ℕ) * h) a T δ)
        (dusartBoxCountingErrorBudget m h x a T δ) + (m + 3 : ℕ) * h / 2 :=
  abs_psi_sub_le_dusartBoxCountingBudget m hh hx ha haT hT hδ hg

example {A X : ℝ} (h : HasDusartBoxCountingBudget A X) : HasDusartBoxLogFourthBudget A X :=
  hasDusartBoxLogFourthBudget_of_counting h

example {A X : ℝ} (h : HasDusartBoxCountingBudget A X) : HasPsiLogFourthError A X :=
  hasPsiLogFourthError_of_dusartBoxCountingBudget h

example (h : HasDusartBoxCountingBudget (1 / 2) (4e18)) :
    ∀ x : ℝ, 4e18 ≤ x → |θ x - x| ≤ (648 / 1000) * x / (Real.log x) ^ 4 :=
  hasThetaLogFourthError_648_of_dusartBoxCountingBudget h

end PrimeFactorUnimodality.Tests
