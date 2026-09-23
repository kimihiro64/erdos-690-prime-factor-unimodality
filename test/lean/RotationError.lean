import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.RotationError

/-! # Exact interfaces and boundary cases for normalized xi evaluation -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex

example (p w : ℂ) :
    p * exp w = ((‖p‖ * Real.exp w.re : ℝ) : ℂ) * exp (I * (arg p + w.im)) := by
  exact Complex.mul_exp_eq_norm_exp_re_mul_rotation p w

example (a b : ℝ) :
    ‖exp (I * a) - exp (I * b)‖ ≤ |a - b| := by
  exact Complex.norm_exp_I_mul_ofReal_sub_le a b

example (a b : ℝ) (z w : ℂ) :
    ‖exp (I * a) * z - exp (I * b) * w‖ ≤ ‖z - w‖ + ‖w‖ * |a - b| := by
  exact Complex.norm_rotated_sub_rotated_le a b z w

example (a b : ℝ) (z w : ℂ) :
    |(exp (I * a) * z).re - (exp (I * b) * w).re| ≤ ‖z - w‖ + ‖w‖ * |a - b| := by
  exact Complex.abs_re_rotated_sub_le a b z w

example (z : ℂ) : z * exp 0 = ((‖z‖ : ℝ) : ℂ) * exp (I * arg z) := by
  simpa using mul_exp_eq_norm_exp_re_mul_rotation z 0

example (a : ℝ) (z : ℂ) : ‖exp (I * a) * z‖ = ‖z‖ := by simp [norm_mul]

example (a b : ℝ) {z w : ℂ} {L : ℝ} (hL : 0 < L) (hz : L ≤ ‖z‖) (hw : L ≤ ‖w‖) :
    ‖exp (I * a) / z - exp (I * b) / w‖ ≤ ‖z - w‖ / L ^ 2 + |a - b| / L :=
  norm_rotation_div_sub_le a b hL hz hw

end

end PrimeFactorUnimodality.Tests
