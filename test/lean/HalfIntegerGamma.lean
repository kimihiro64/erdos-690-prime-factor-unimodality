import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.HalfIntegerNorm

/-! Reflection, signed heights and the first odd-line Gamma majorant. -/

open Complex

example (t : Real) :
    ‖Gamma ((1 / 2 : Complex) + (t : Complex) * I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := norm_Gamma_half_add_mul_I_sq t

example (u : Real) :
    ‖Gamma ((3 / 2 : Complex) + ((u / 2 : Real) : Complex) * I)‖ *
        Real.exp (Real.pi * u / 4) ≤ Real.sqrt (2 * Real.pi) * (|u| + 1) / 2 := by
  have hr : |u| + 2 - 1 = |u| + 1 := by ring
  simpa [hr, show (2 : Complex) + 1 = 3 by norm_num] using norm_Gamma_odd_half_mul_exp_le 1 u

example (m : Nat) :
    ‖Gamma ((m : Complex) + 1 / 2)‖ ≤ Real.sqrt (2 * Real.pi) * ((m : Real) - 1 / 2) ^ m := by
  simpa using norm_Gamma_nat_add_half_mul_exp_le m 0

example (u : Real) :
    ‖Gamma ((1 / 2 : Complex) + (-u : Real) * I)‖ * Real.exp (Real.pi * (-u) / 2) ≤
      Real.sqrt (2 * Real.pi) := norm_Gamma_half_add_mul_I_mul_exp_le (-u)
