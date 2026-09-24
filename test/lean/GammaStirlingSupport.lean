import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogStirlingLimit
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.ShiftedReciprocal

/-! Full complex normalization and endpoint cases for horizontal reciprocal powers. -/

open Complex Filter MeasureTheory Set
open scoped Topology

example :
    Tendsto (fun n : ℕ => Real.log n.factorial + n - ((n : ℝ) + 1 / 2) * Real.log n)
      atTop (𝓝 (Real.log (2 * Real.pi) / 2)) :=
  Stirling.tendsto_log_factorial_normalization

-- The endpoint limit is valid for arbitrary fixed shifts, not just positive real parts.
example :
    Tendsto (fun n : ℕ => (Real.log n.factorial : ℂ) + n +
      (-2 + I) * (Real.log n : ℂ) + (-2 + I) -
      ((-2 + I) + n + 1 / 2) * log ((-2 + I) + n))
      atTop (𝓝 ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ)) :=
  tendsto_log_stirling_endpoint (-2 + I)

example {z : ℂ} (hz : 0 < z.re) : z + (0 : ℝ) ≠ 0 :=
  add_ofReal_ne_zero_of_re_pos hz le_rfl

example {z : ℂ} {x : ℝ} (hx : z + (x : ℂ) ≠ 0) :
    HasDerivAt (fun y : ℝ => (z + (y : ℂ))⁻¹ ^ 0) 0 x := by
  simpa using hasDerivAt_inv_pow_add_ofReal 0 hx

example {z : ℂ} {x : ℝ} (hx : z + (x : ℂ) ≠ 0) :
    HasDerivAt (fun y : ℝ => (z + (y : ℂ))⁻¹ ^ 2)
      (-2 * (z + (x : ℂ))⁻¹ ^ 3) x := by
  simpa using hasDerivAt_inv_pow_add_ofReal 2 hx

example {z : ℂ} (hz : 0 < z.re) : ‖z⁻¹ ^ 2‖ ≤ z.re ^ (-2 : ℝ) := by
  simpa using norm_inv_pow_add_ofReal_le 2 hz (le_refl (0 : ℝ))

example {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ => (z + (x : ℂ))⁻¹ ^ 2) (Ioi 0) :=
  integrableOn_inv_pow_add_ofReal (by norm_num) hz
