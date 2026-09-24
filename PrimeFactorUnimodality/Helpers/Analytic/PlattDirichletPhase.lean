import PrimeFactorUnimodality.Helpers.Analytic.PlattDirichletTerms
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.RotationError

set_option autoImplicit false

/-! # Enclosed real logarithms supply the actual Dirichlet weights and shifts

One logarithm controls both the frequency shift and the unit complex phase.
The center height multiplies the phase uncertainty, and amplitude and
phase evaluation errors remain separate. No exact transcendental input
is required from the finite evaluator.
-/

namespace PrimeFactorUnimodality

/-- The actual positive-index weight is a reciprocal square root times a unit rotation. -/
theorem plattDirichletWeight_eq_rotation (t₀ : ℝ) {j : ℕ} (hj : 0 < j) :
    plattDirichletWeight t₀ j =
      Complex.exp (Complex.I * ((-t₀ * Real.log ((j : ℝ) * Real.sqrt Real.pi) : ℝ) : ℂ)) *
        ((1 / Real.sqrt j : ℝ) : ℂ) := by
  have hp : 0 < (j : ℝ) * Real.sqrt Real.pi := by positivity
  have ha : (j : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt j := by
    rw [Real.rpow_neg (Nat.cast_nonneg j), ← Real.sqrt_eq_rpow, one_div]
  rw [plattDirichletWeight, ha, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le]
  push_cast
  conv_lhs => rw [mul_comm]
  congr 1
  congr 1
  ring

/-- A log enclosure gives a shift enclosure with its exact positive normalization. -/
theorem abs_plattDirichletShift_sub_le {j : ℕ} {L δ : ℝ}
    (hL : |Real.log ((j : ℝ) * Real.sqrt Real.pi) - L| ≤ δ) :
    |plattDirichletShift j - L / (2 * Real.pi)| ≤ δ / (2 * Real.pi) := by
  rw [plattDirichletShift, ← sub_div, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  exact div_le_div_of_nonneg_right hL (by positivity)

/-- Enclosed log and amplitude data give a full complex weight error. -/
theorem norm_plattDirichletWeight_sub_log_approx_le (t₀ : ℝ) {j : ℕ} (hj : 0 < j)
    {L δ a η : ℝ} (hL : |Real.log ((j : ℝ) * Real.sqrt Real.pi) - L| ≤ δ)
    (ha : |1 / Real.sqrt j - a| ≤ η) :
    ‖plattDirichletWeight t₀ j -
        Complex.exp (Complex.I * ((-t₀ * L : ℝ) : ℂ)) * (a : ℂ)‖ ≤
      η + |a| * (|t₀| * δ) := by
  rw [plattDirichletWeight_eq_rotation t₀ hj]
  have ht := Complex.norm_rotated_sub_rotated_le
    (-t₀ * Real.log ((j : ℝ) * Real.sqrt Real.pi)) (-t₀ * L) (1 / Real.sqrt j : ℝ) a
  have he : |(-t₀ * Real.log ((j : ℝ) * Real.sqrt Real.pi)) - (-t₀ * L)| =
      |t₀| * |Real.log ((j : ℝ) * Real.sqrt Real.pi) - L| := by
    rw [← mul_sub, abs_mul, abs_neg]
  simp only [he, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at ht
  exact ht.trans (add_le_add ha (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hL (abs_nonneg t₀)) (abs_nonneg a)))

end PrimeFactorUnimodality
