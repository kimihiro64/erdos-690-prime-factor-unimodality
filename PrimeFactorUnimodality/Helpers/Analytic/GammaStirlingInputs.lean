import PrimeFactorUnimodality.Helpers.Analytic.GammaStirlingBounds
import PrimeFactorUnimodality.Helpers.Analytic.GammaStirlingRational
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.LogCartesian

/-! # Three real-function enclosures supply a rational Stirling input

The exact correction evaluator needs no error allowance. Only the logarithm
of the squared norm, the branch-fixed arctangent, and `log (2*pi)` contribute
to the logarithmic arithmetic error. This theorem is shared by all sample rows.
-/

namespace PrimeFactorUnimodality

open Complex

/-- Exact rational assembly retains the errors of all three transcendental inputs. -/
theorem norm_stirlingApprox_sub_rationalInput_le (M : ℕ) (z : RationalPoint)
    (hz : 0 < z.re) (ell theta c : ℚ) {ε δ η : ℝ}
    (hell : |Real.log ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) - (ell : ℝ)| ≤ ε)
    (htheta : |Real.arctan ((z.im : ℝ) / (z.re : ℝ)) - (theta : ℝ)| ≤ δ)
    (hc : |Real.log (2 * Real.pi) - (c : ℝ)| ≤ η) :
    ‖gammaStirlingApprox M z.toComplex - (gammaStirlingRationalInput M z ell theta c).toComplex‖ ≤
      ‖z.toComplex - 1 / 2‖ * (ε / 2 + δ) + η / 2 := by
  have hzC : 0 < z.toComplex.re := by
    change (0 : ℝ) < (z.re : ℝ)
    exact_mod_cast hz
  have hlog : ‖log z.toComplex - ((ell / 2 : ℚ) : ℂ) - (theta : ℂ) * I‖ ≤ ε / 2 + δ := by
    have h := norm_log_sub_cartesian_le hzC hell htheta
    push_cast at h ⊢
    exact h
  have hconst : ‖(((Real.log (2 * Real.pi) - (c : ℝ)) / 2 : ℝ) : ℂ)‖ ≤ η / 2 := by
    rw [norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right hc (by norm_num)
  have he : gammaStirlingApprox M z.toComplex -
      (gammaStirlingRationalInput M z ell theta c).toComplex =
      (z.toComplex - 1 / 2) * (log z.toComplex - ((ell / 2 : ℚ) : ℂ) - (theta : ℂ) * I) +
        (((Real.log (2 * Real.pi) - (c : ℝ)) / 2 : ℝ) : ℂ) := by
    rw [toComplex_gammaStirlingRationalInput, gammaStirlingApprox]
    push_cast
    ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hlog (norm_nonneg _)) hconst

end PrimeFactorUnimodality
