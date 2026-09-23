import PrimeFactorUnimodality.Helpers.Analytic.KadiriTransformChecks

/-! # Exact R6 interfaces and branch regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open LeanCert.Core

example (θ a₀ a₁ w lower : ℚ) (precision : ℤ) (depth : ℕ)
    (hprecision : precision ≤ 0)
    (h : checkKadiriTransform θ a₀ a₁ w lower precision depth = true) :
    (lower : ℝ) ≤ kadiriTransformGapClosedForm θ a₀ a₁ w := by
  exact PrimeFactorUnimodality.kadiriTransform_le_of_check θ a₀ a₁ w lower precision depth hprecision h

example (precision : ℤ) (depth : ℕ)
    (hprecision : precision ≤ 0)
    (h : ∀ i : Fin 4, checkKadiriSixTransformRow i precision depth = true) :
    KadiriSixTransformBounds := by
  exact PrimeFactorUnimodality.kadiriSixTransformBounds_of_checks precision depth hprecision h

example : checkKadiriTransform 0 1 1 1 0 (-8) 2 = false := by decide +kernel

example : kadiriSixTransformRow 0 = (9 / 100, 18) ∧
    kadiriSixTransformRow 1 = (69 / 100, 22) ∧
    kadiriSixTransformRow 2 = (79 / 100, 23) ∧
    kadiriSixTransformRow 3 = (1, 23) := by norm_num [kadiriSixTransformRow]

end

end PrimeFactorUnimodality.Tests
