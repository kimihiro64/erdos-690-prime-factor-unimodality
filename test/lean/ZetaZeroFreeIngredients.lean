import PrimeFactorUnimodality.Helpers.Analytic.ZetaRealPole

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

end PrimeFactorUnimodality.Tests
