import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxLogFourth

/-! # Exact provider-boundary regression checks

The scalar budget supplies the psi predicate at every point above the
cutoff. The existing sharp correction gives exactly `648/1000` from `4e18`,
without turning the remaining zero-location or parameter inputs into facts.
-/

namespace PrimeFactorUnimodality.Tests

example {A X : ℝ} (h : HasDusartBoxLogFourthBudget A X) : HasPsiLogFourthError A X :=
  hasPsiLogFourthError_of_dusartBoxBudget h

example {A X : ℝ} (hX : (4e18 : ℝ) ≤ X) (h : HasDusartBoxLogFourthBudget A X) :
    HasThetaLogFourthError (A + 148 / 1000) X :=
  hasThetaLogFourthError_of_dusartBoxBudget hX h

example (h : HasDusartBoxLogFourthBudget (1 / 2) (4e18)) :
    ∀ x : ℝ, 4e18 ≤ x → |Chebyshev.theta x - x| ≤ (648 / 1000) * x / (Real.log x) ^ 4 :=
  hasThetaLogFourthError_648_of_dusartBoxBudget h

end PrimeFactorUnimodality.Tests
