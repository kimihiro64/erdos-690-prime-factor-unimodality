import PrimeFactorUnimodality.Helpers.Analytic.ZetaRealPole
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiZeroContribution

set_option autoImplicit false

/-! # The explicit classical zero-free-region inequality

Combine the `3,4,1` trigonometric polynomial, the unit real pole bound,
the gamma estimate, and the negative contribution of a putative zero.
The resulting inequality has only elementary explicit terms. It is the
starting inequality, not yet Dusart's required numerical zero-free region.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The real pole contribution away from the real axis. -/
def zeroFreePoleTerm (σ t : ℝ) : ℝ := (σ - 1) / ((σ - 1) ^ 2 + t ^ 2)

/-- The already-proved upper bound for the archimedean gamma contribution. -/
def zeroFreeGammaTerm (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (|t| / 2 + 3) + 1 / 2 - (1 / 2 : ℝ) * Real.log Real.pi

private theorem re_complex_pole_eq (σ t : ℝ) :
    (1 / ((σ : ℂ) + t * I - 1)).re = zeroFreePoleTerm σ t := by
  simp [one_div, inv_re, normSq_apply, zeroFreePoleTerm, pow_two]

/-- The xi constant plus elementary terms bound the zeta logarithmic derivative. -/
theorem re_neg_logDeriv_riemannZeta_le_explicit {σ : ℝ}
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (t : ℝ) :
    (-deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I)).re ≤
      -(logDeriv riemannXi 0).re + zeroFreePoleTerm σ t + zeroFreeGammaTerm t := by
  have h := re_neg_logDeriv_riemannZeta_le_xi
    (s := (σ : ℂ) + t * I) (by simpa using hσ) (by simpa using hσ₂)
  have hz := re_logDeriv_riemannXi_zero_le (s := (σ : ℂ) + t * I) (by simpa using hσ)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
    zero_add, add_zero, re_complex_pole_eq] at h
  dsimp [zeroFreeGammaTerm]
  linarith

/-- Every actual xi zero satisfies the fully explicit `3,4,1` constraint. -/
theorem xi_zero_three_four_one_constraint {ρ : ℂ} (hρ : riemannXi ρ = 0)
    {σ : ℝ} (hσ : 1 < σ) (hσ₂ : σ ≤ 2) :
    4 / (σ - ρ.re) ≤ 3 / (σ - 1) + 3 -
      (5 / 2 : ℝ) * (Real.log (4 * Real.pi) - Real.eulerMascheroniConstant - 2) +
      4 * zeroFreePoleTerm σ ρ.im + zeroFreePoleTerm σ (2 * ρ.im) +
      4 * zeroFreeGammaTerm ρ.im + zeroFreeGammaTerm (2 * ρ.im) := by
  have hpos := three_four_one_re_neg_logDeriv_riemannZeta_nonneg hσ ρ.im
  have hreal := re_neg_logDeriv_riemannZeta_le_pole_add_one hσ
  have hzero := re_neg_logDeriv_riemannZeta_le_zero hρ hσ hσ₂
  have hdouble := re_neg_logDeriv_riemannZeta_le_explicit hσ hσ₂ (2 * ρ.im)
  rw [re_complex_pole_eq] at hzero
  change _ ≤ -(logDeriv riemannXi 0).re - 1 / (σ - ρ.re) +
    zeroFreePoleTerm σ ρ.im + zeroFreeGammaTerm ρ.im at hzero
  rw [re_logDeriv_riemannXi_zero_eq] at hzero hdouble
  simp only [div_eq_mul_inv] at hpos hreal hzero hdouble ⊢
  linarith

/-- An elementary strict reverse inequality excludes the proposed xi zero. -/
theorem riemannXi_ne_zero_of_three_four_one {ρ : ℂ} {σ : ℝ}
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2)
    (hexclude : 3 / (σ - 1) + 3 -
      (5 / 2 : ℝ) * (Real.log (4 * Real.pi) - Real.eulerMascheroniConstant - 2) +
      4 * zeroFreePoleTerm σ ρ.im + zeroFreePoleTerm σ (2 * ρ.im) +
      4 * zeroFreeGammaTerm ρ.im + zeroFreeGammaTerm (2 * ρ.im) < 4 / (σ - ρ.re)) :
    riemannXi ρ ≠ 0 := by
  intro hρ
  exact (not_le_of_gt hexclude) (xi_zero_three_four_one_constraint hρ hσ hσ₂)

end

end PrimeFactorUnimodality
