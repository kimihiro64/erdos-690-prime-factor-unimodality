import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaReality
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaResidueNorm
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaRightBound

set_option autoImplicit false

/-! # A two-sided exponential envelope for the actual zeta window

The positive-frequency contour estimate and proved conjugation symmetry
control both signs. There are exactly two terms: the displaced integral and
the unique crossed zeta pole. Both coefficients retain every polynomial order.
-/

open scoped FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- The two coefficients: contour integral (`false`) and zeta residue (`true`). -/
def plattZetaEnvelopeCoeff (m k : ℕ) (t₀ h : ℝ) : Bool → ℝ
  | false => plattZetaRightFactor m * plattScalarCMajorant m k t₀ h *
      Real.exp ((plattRightShift m) ^ 2 / (2 * h ^ 2))
  | true => 2 * Real.pi * ‖plattZetaContourResidueValue k t₀ h 0‖

/-- Decay rates of the displaced contour and the unique zeta pole. -/
def plattZetaEnvelopeRate (m : ℕ) : Bool → ℝ
  | false => 2 * Real.pi * plattRightShift m
  | true => Real.pi

theorem plattZetaEnvelopeCoeff_nonneg (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (i : Bool) :
    0 ≤ plattZetaEnvelopeCoeff m k t₀ h i := by
  cases i with
  | false =>
    exact mul_nonneg (mul_nonneg (plattZetaRightFactor_nonneg m)
      (plattScalarCMajorant_nonneg m k hm ht₀ hh)) (Real.exp_pos _).le
  | true => simp only [plattZetaEnvelopeCoeff]; positivity

theorem plattZetaEnvelopeRate_pos (m : ℕ) (i : Bool) :
    0 < plattZetaEnvelopeRate m i := by
  cases i <;> simp only [plattZetaEnvelopeRate, plattRightShift] <;> positivity

/-- Both frequency signs satisfy the actual contour-plus-pole exponential bound. -/
theorem norm_fourier_plattZetaWindow_le_envelope (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) :
    ‖𝓕 (plattZetaWindow k t₀ h) x‖ ≤
      ∑ i : Bool, plattZetaEnvelopeCoeff m k t₀ h i *
        Real.exp (-plattZetaEnvelopeRate m i * |x|) := by
  have hn : ‖𝓕 (plattZetaWindow k t₀ h) x‖ =
      ‖𝓕 (plattZetaWindow k t₀ h) |x|‖ := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, norm_fourier_plattZetaWindow_neg]
  rw [hn]
  apply (norm_fourier_plattZetaWindow_le_right m k hm ht₀ hh |x|).trans_eq
  rw [norm_plattZetaContourResidueValue_eq_zero_mul_exp]
  simp only [Fintype.sum_bool, plattZetaEnvelopeCoeff, plattZetaEnvelopeRate]
  rw [show plattRightShift m ^ 2 / (2 * h ^ 2) -
    2 * Real.pi * |x| * plattRightShift m =
      plattRightShift m ^ 2 / (2 * h ^ 2) +
        -(2 * Real.pi * plattRightShift m) * |x| by ring, Real.exp_add]
  ring

end

end PrimeFactorUnimodality
