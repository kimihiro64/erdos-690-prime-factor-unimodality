import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.LogDampedPolynomial

/-! # Regression statements for the decreasing logarithmic error -/

namespace Real.Tests

open Real

example (n : ℕ) {a q t : ℝ} (ha : 0 < a) (ht : 1 < t) :
    logDampedPower a q t ≤ ((n.factorial : ℝ) ^ 2 / a ^ n) * logDampedPower 0 (q - 1) t :=
  logDampedPower_le_polynomial n ha ht

example {a q t : ℝ} (ha : 0 < a) (ht : 1 < t) :
    logDampedPower a q t ≤ logDampedPower 0 (q - 1) t := by
  simpa using logDampedPower_le_polynomial 0 ha ht

end Real.Tests
