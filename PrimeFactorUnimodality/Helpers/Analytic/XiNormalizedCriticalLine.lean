import PrimeFactorUnimodality.Helpers.Analytic.TuringCountPhase
import PrimeFactorUnimodality.Helpers.Analytic.XiCriticalLine
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.RotationError

/-! # Positive rescaling of xi to a rotated zeta value

The shifted Gamma logarithm and the pole's principal argument give an exact
positive amplitude times a unit rotation. Removing that amplitude avoids
the exponentially small magnitude of xi without changing its signs.
The phase is the existing counting phase, not an unproved Hardy-Z convention.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The positive amplitude removed from xi on the critical line. -/
def xiCriticalLineScale (t : ℝ) : ℝ :=
  ‖(1 / 2 : ℂ) + t * I - 1‖ * Real.exp (xiGammaLog ((1 / 2 : ℂ) + t * I)).re

/-- The rotated real zeta value has the same sign as xi, with its exponential decay removed. -/
def xiNormalizedValue (t : ℝ) : ℝ :=
  (exp (I * turingCountingPhase t) * riemannZeta ((1 / 2 : ℂ) + t * I)).re

/-- The scale is strictly positive at every real height, including zero and negative heights. -/
theorem xiCriticalLineScale_pos (t : ℝ) : 0 < xiCriticalLineScale t := by
  apply mul_pos _ (Real.exp_pos _)
  apply norm_pos_iff.mpr
  intro he
  have hr := congrArg Complex.re he
  norm_num at hr

/-- Exact complex factorization into the positive amplitude and normalized rotated zeta. -/
theorem riemannXi_criticalLine_eq_scale_mul (t : ℝ) :
    riemannXi ((1 / 2 : ℂ) + t * I) = (xiCriticalLineScale t : ℂ) *
      (exp (I * turingCountingPhase t) * riemannZeta ((1 / 2 : ℂ) + t * I)) := by
  let s : ℂ := (1 / 2 : ℂ) + t * I
  have hs : 0 < s.re := by dsimp [s]; norm_num
  have hs1 : s ≠ 1 := by intro he; have hr := congrArg Complex.re he; norm_num [s] at hr
  have hγ : 0 < (s / 2 + 1).re := by dsimp [s]; norm_num
  have he : riemannXi s = (s - 1) * exp (xiGammaLog s) * riemannZeta s := by
    rw [riemannXi_eq_shifted_gamma_product_of_re_pos hs hs1]
    dsimp [xiGammaLog]
    rw [show gammaRightLog (s / 2 + 1) - s / 2 * (Real.log Real.pi : ℂ) =
      gammaRightLog (s / 2 + 1) + -(s / 2 * (Real.log Real.pi : ℂ)) by ring,
      exp_add, exp_gammaRightLog hγ,
      show -(s / 2 * (Real.log Real.pi : ℂ)) = -(s / 2) * Real.log Real.pi by ring]
    ring
  rw [he, mul_exp_eq_norm_exp_re_mul_rotation]
  simp only [xiCriticalLineScale, turingCountingPhase, ofReal_add, s, mul_assoc, add_comm]

/-- Taking real parts preserves the exact positive amplitude. -/
theorem xiCriticalLineValue_eq_scale_mul (t : ℝ) :
    xiCriticalLineValue t = xiCriticalLineScale t * xiNormalizedValue t := by
  have h := congrArg Complex.re (riemannXi_criticalLine_eq_scale_mul t)
  simpa only [xiCriticalLineValue, xiNormalizedValue, mul_re, ofReal_re, ofReal_im,
    zero_mul, sub_zero] using h

/-- The normalized complex value is exactly real, including at zeros. -/
theorem xiNormalizedComplex_im (t : ℝ) :
    (exp (I * turingCountingPhase t) * riemannZeta ((1 / 2 : ℂ) + t * I)).im = 0 := by
  have h := congrArg Complex.im (riemannXi_criticalLine_eq_scale_mul t)
  have he : xiCriticalLineScale t *
      (exp (I * turingCountingPhase t) * riemannZeta ((1 / 2 : ℂ) + t * I)).im = 0 := by
    simpa only [riemannXi_criticalLine_im, mul_im, ofReal_re, ofReal_im,
      zero_mul, zero_add, add_zero] using h.symm
  exact (mul_eq_zero.mp he).resolve_left (xiCriticalLineScale_pos t).ne'

/-- Positive signs are preserved by the normalization. -/
theorem xiCriticalLineValue_pos_iff_normalized (t : ℝ) :
    0 < xiCriticalLineValue t ↔ 0 < xiNormalizedValue t := by
  rw [xiCriticalLineValue_eq_scale_mul]
  constructor <;> intro h <;> nlinarith [xiCriticalLineScale_pos t]

/-- Negative signs are preserved by the normalization. -/
theorem xiCriticalLineValue_neg_iff_normalized (t : ℝ) :
    xiCriticalLineValue t < 0 ↔ xiNormalizedValue t < 0 := by
  rw [xiCriticalLineValue_eq_scale_mul]
  constructor <;> intro h <;> nlinarith [xiCriticalLineScale_pos t]

end

end PrimeFactorUnimodality
