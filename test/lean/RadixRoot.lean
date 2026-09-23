import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RadixRoot

/-! # Rational checks and exact interface regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Fourier ZMod

example (n : ℕ) : ‖radixRoot n‖ = 1 := by
  exact Fourier.norm_radixRoot n

example (n k : ℕ) :
    radixRoot n ^ k = exp (I * ((2 * Real.pi * k / (2 ^ n) : ℝ) : ℂ)) := by
  exact Fourier.radixRoot_pow n k

example (n : ℕ) : radixRoot (n + 1) ^ 2 = radixRoot n := by
  exact Fourier.radixRoot_succ_sq n

example : radixRoot 0 = 1 := by
  simpa [radixRoot] using (ZMod.stdAddChar_one_pow_card (N := 1))
example (n : ℕ) : radixRoot n ^ 0 = exp (I * ((0 : ℝ) : ℂ)) := by simp

end

end PrimeFactorUnimodality.Tests
