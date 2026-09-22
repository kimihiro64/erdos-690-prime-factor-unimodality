import PrimeFactorUnimodality.Mathlib.Analysis.Complex.Hadamard.Integral

set_option autoImplicit false

/-! # Fractional contour integrability and off-midline, repeated zeros

The fractional majorant works even for positive lines below one. The
interchange accepts unequal real parts and a repeated zero, preserving
the divisor-index interpretation instead of replacing it with a zero set.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex MeasureTheory

example : Integrable (fun t : ℝ => ‖(1 / 4 : ℂ) + (t : ℂ) * I‖⁻¹ ^ (3 / 2 : ℝ)) := by
  simpa using integrable_inv_rpow_norm_vertical (a := 1 / 4) (r := 3 / 2)
    (by norm_num) (by norm_num)

private def zeros (i : Fin 3) : ℂ := if i = 1 then (3 / 4 : ℂ) + I else (1 / 4 : ℂ) + I

example : zeros 0 = zeros 2 ∧ (zeros 0).re ≠ (zeros 1).re := by norm_num [zeros]

example {H : ℝ → ℂ} (hH : Integrable H)
    (hBound : ∀ t, ‖H t‖ ≤ 1 / ‖(3 / 2 : ℂ) + (t : ℂ) * I‖ ^ 2) :
    (∑' i : Fin 3, ∫ t : ℝ,
      H t * (1 / ((3 / 2 : ℂ) + (t : ℂ) * I - zeros i) + 1 / zeros i)) =
      ∫ t : ℝ, H t * (∑' i : Fin 3,
        (1 / ((3 / 2 : ℂ) + (t : ℂ) * I - zeros i) + 1 / zeros i)) := by
  have hn (i : Fin 3) : zeros i ≠ 0 := by
    intro heq
    have hi := congrArg Complex.im heq
    fin_cases i <;> norm_num [zeros] at hi
  have hr (i : Fin 3) : (zeros i).re ≤ 1 := by fin_cases i <;> norm_num [zeros]
  have hb : ∀ t, ‖H t‖ ≤ (1 : ℝ) / ‖((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ ^ 2 := by
    simpa using hBound
  simpa using tsum_integral_mul_hadamardAtoms (c := 3 / 2) (B := 1) (C := 1)
    (by norm_num) (by norm_num) (by norm_num) hn hr Summable.of_finite hH hb

end

end PrimeFactorUnimodality.Tests
