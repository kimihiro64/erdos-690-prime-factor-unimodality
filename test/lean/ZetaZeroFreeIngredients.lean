import PrimeFactorUnimodality.Helpers.Analytic.ZetaRealPole
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiLogDerivative

set_option autoImplicit false

/-! # Regression checks for the explicit zero-free-region ingredients

These checks cover the pole's unit coefficient, its extension off the real
axis, and trigonometric positivity. They do not assert a completed zero-free
region or a fixed-cutoff prime-number estimate.
-/

open Complex

namespace PrimeFactorUnimodality.Tests

example : 2 ≤ (riemannZeta (3 / 2 : ℂ)).re := by
  have h := one_div_sub_one_le_re_riemannZeta (by norm_num : (1 : ℝ) < 3 / 2)
  norm_num at h ⊢
  exact h

example : ‖riemannZeta (3 / 2 : ℂ)‖ ≤ 3 := by
  have h := norm_riemannZeta_real_le_pole_add_one (by norm_num : (1 : ℝ) < 3 / 2)
  norm_num at h ⊢
  exact h

example (t : ℝ) :
    ‖deriv riemannZeta ((3 / 2 : ℂ) + t * I) /
      riemannZeta ((3 / 2 : ℂ) + t * I)‖ ≤ 3 := by
  have h := norm_logDeriv_riemannZeta_le_pole_add_one
    (s := (3 / 2 : ℂ) + t * I) (by norm_num)
  norm_num at h ⊢
  exact h

example {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
      4 * (-deriv riemannZeta ((σ : ℂ) + t * I) /
        riemannZeta ((σ : ℂ) + t * I)).re +
      (-deriv riemannZeta ((σ : ℂ) + (2 * t : ℝ) * I) /
        riemannZeta ((σ : ℂ) + (2 * t : ℝ) * I)).re :=
  three_four_one_re_neg_logDeriv_riemannZeta_nonneg hσ t

example (σ : ℝ) (hσ : 0 < σ) :
    (∫ u in Set.Ioi (1 : ℝ), -(Real.log u : ℂ) * zetaAbelFractKernel (σ : ℂ) u).re ≤ 0 :=
  re_zetaAbelIntegral_derivative_nonpos hσ

example (z : ℂ) (hz : 1 ≤ z.re) (N : ℕ) (hN : 1 ≤ N) :
    (digamma z).re ≤ Real.log ((N : ℝ) + 1) + ‖z - 1‖ / N :=
  re_digamma_le_log_add_tail hz hN

example (t : ℝ) : (digamma ((1 : ℂ) + t * I)).re ≤ Real.log (|t| + 2) + 1 := by
  have h := re_digamma_le_log_norm_sub_one_add_two
    (z := (1 : ℂ) + t * I) (by simp)
  simpa [norm_mul, norm_real, Real.norm_eq_abs, add_sub_cancel_left] using h

example (t : ℝ) :
    (-deriv riemannZeta ((3 / 2 : ℂ) + t * I) /
      riemannZeta ((3 / 2 : ℂ) + t * I)).re ≤
      -(logDeriv riemannXi ((3 / 2 : ℂ) + t * I)).re +
        (1 / ((3 / 2 : ℂ) + t * I - 1)).re +
        ((1 / 2 : ℝ) * Real.log (|t| / 2 + 3) + 1 / 2 -
          (1 / 2 : ℝ) * Real.log Real.pi) := by
  simpa using re_neg_logDeriv_riemannZeta_le_xi
    (s := (3 / 2 : ℂ) + t * I) (by norm_num) (by norm_num)

end PrimeFactorUnimodality.Tests
