import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiMultiplicity
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation

/-! # No real zeros of the entire xi function

The pinned Abel continuation has nonnegative fractional-part remainder.
It makes zeta strictly negative on the real interval from one half to one.
The gamma prefactor and xi's functional equation then exclude every real
xi zero, including the completed values at zero and one.

This uses Matteo Cipollina's Apache-2.0 Abel continuation from PNT revision
`f6147e7572ab3abe5428101bc0b13627bcb005df`. Its continuation domain only
requires real part greater than one tenth; reflection supplies the left
half, so no extension of that dependency's domain is assumed.
-/

namespace PrimeFactorUnimodality
noncomputable section
open Complex MeasureTheory Set

/-- The Abel remainder makes zeta strictly negative between one half and one. -/
theorem riemannZeta_re_neg_of_half_le_of_lt_one {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) :
    (riemannZeta (σ : ℂ)).re < 0 := by
  have hpos : 0 < σ := by linarith
  have hi := ZetaAbelFractKernel.integrableOn_Ioi (σ : ℂ) (by simpa using hpos)
  have hnn : 0 ≤ (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel (σ : ℂ) u).re := by
    have heq : (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel (σ : ℂ) u).re =
        ∫ u in Ioi (1 : ℝ), (zetaAbelFractKernel (σ : ℂ) u).re := (integral_re hi).symm
    rw [heq]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_of_lt (zero_lt_one.trans hu)
    have he : zetaAbelFractKernel (σ : ℂ) u = ((Int.fract u * u ^ (-σ - 1) : ℝ) : ℂ) := by
      simp only [zetaAbelFractKernel, ofReal_mul]
      rw [show -(σ : ℂ) - 1 = ((-σ - 1 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_cpow hu0]
    rw [he, ofReal_re]
    exact mul_nonneg (Int.fract_nonneg u) (Real.rpow_nonneg hu0 _)
  have hdom : (σ : ℂ) ∈ zetaAbelContinuationDomain := by
    constructor
    · exact_mod_cast hσ1.ne
    · change (1 / 10 : ℝ) < σ
      linarith
  rw [riemannZeta_eq_zetaAbelContinuationFormula _ hdom]
  have hrat : (1 : ℝ) + 1 / (σ - 1) < 0 := by
    have he : 1 + 1 / (σ - 1) = σ / (σ - 1) := by
      field_simp [sub_ne_zero.mpr hσ1.ne]
      ring
    rw [he]
    exact div_neg_of_pos_of_neg hpos (by linarith)
  have hr : (zetaAbelContinuationFormula (σ : ℂ)).re =
      1 + 1 / (σ - 1) - σ * (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel (σ : ℂ) u).re := by
    simp only [zetaAbelContinuationFormula, ← ofReal_one, ← ofReal_sub, ← ofReal_div,
      add_re, sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [hr]
  nlinarith

/-- Xi has no real zeros, unconditionally and including its completed endpoints. -/
theorem riemannXi_ofReal_ne_zero (x : ℝ) : riemannXi (x : ℂ) ≠ 0 := by
  have hright {σ : ℝ} (hσ : 1 / 2 ≤ σ) : riemannXi (σ : ℂ) ≠ 0 := by
    by_cases h1 : 1 ≤ σ
    · exact riemannXi_ne_zero_of_one_le_re (by simpa using h1)
    intro hz
    have hζ : riemannZeta (σ : ℂ) = 0 :=
      (riemannXi_eq_zero_iff_riemannZeta_eq_zero (by simpa using (show 0 < σ by linarith))
        (by exact_mod_cast (lt_of_not_ge h1).ne)).mp hz
    have hn := riemannZeta_re_neg_of_half_le_of_lt_one hσ (lt_of_not_ge h1)
    simp only [hζ, zero_re, lt_self_iff_false] at hn
  by_cases hx : 1 / 2 ≤ x
  · exact hright hx
  have h := hright (σ := 1 - x) (by linarith)
  simpa only [ofReal_sub, ofReal_one, riemannXi_one_sub] using h

end
end PrimeFactorUnimodality
