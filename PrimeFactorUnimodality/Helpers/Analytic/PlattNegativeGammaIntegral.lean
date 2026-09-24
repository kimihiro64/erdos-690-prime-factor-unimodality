import PrimeFactorUnimodality.Helpers.Analytic.PlattGammaIntegral
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.NegativeHalfNorm

set_option autoImplicit false

/-! # The negative-line Gamma window

The integral left after shifting toward negative odd real parts is controlled
by the positive-line scalar majorant. The real part `-3/2` needs a correction
factor `8/3`; shifts starting at `-5/2` use factor one. These are integral
bounds, not a contour-shift identity or a substitute for the residue sum.
-/

open MeasureTheory

namespace PrimeFactorUnimodality

noncomputable section

/-- The correction retains the exceptional lowest admissible odd shift. -/
def plattNegativeGammaFactor (m : ℕ) : ℝ := if m < 2 then 8 / 3 else 1

/-- Either branch is nonnegative, as required by integral monotonicity. -/
theorem plattNegativeGammaFactor_nonneg (m : ℕ) : 0 ≤ plattNegativeGammaFactor m := by
  unfold plattNegativeGammaFactor
  split_ifs <;> norm_num

/-- The absolute integrand on the line with Gamma real part `-(m+1/2)`. -/
def plattNegativeGammaWindow (m k : ℕ) (t₀ h v : ℝ) : ℝ :=
  ‖Complex.Gamma (-(((m : ℝ) + 1 / 2 : ℝ) : ℂ) +
    (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I)‖ *
    Real.exp (Real.pi * (v + t₀) / 4 - v ^ 2 / (2 * h ^ 2)) *
    ‖((2 * (m : ℝ) + 3 / 2 : ℝ) : ℂ) - (v : ℂ) * Complex.I‖ ^ k

/-- The negative Gamma line contains no poles at any real integration height. -/
theorem continuous_plattNegativeGammaWindow (m k : ℕ) (t₀ h : ℝ) :
    Continuous (plattNegativeGammaWindow m k t₀ h) := by
  have hg := (Complex.continuous_Gamma_neg_nat_sub_half m).comp
    (show Continuous (fun v : ℝ => (v + t₀) / 2) by fun_prop)
  exact (hg.norm.mul (by fun_prop)).mul (by fun_prop)

/-- The corrected opposite-line comparison is retained pointwise before integration. -/
theorem plattNegativeGammaWindow_le (m k : ℕ) (t₀ h v : ℝ) :
    plattNegativeGammaWindow m k t₀ h v ≤
      plattNegativeGammaFactor m * plattGammaWindow m k t₀ h v := by
  have hg :
      ‖Complex.Gamma (-(((m : ℝ) + 1 / 2 : ℝ) : ℂ) +
        (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
      plattNegativeGammaFactor m *
        ‖Complex.Gamma ((((m : ℝ) + 1 / 2 : ℝ) : ℂ) +
          (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I)‖ := by
    by_cases hm : m < 2
    · simpa only [plattNegativeGammaFactor, ite_eq_left hm] using
        Complex.norm_Gamma_neg_nat_sub_half_le m ((v + t₀) / 2)
    · simpa only [plattNegativeGammaFactor, ite_eq_right hm, one_mul] using
        Complex.norm_Gamma_neg_nat_sub_half_le_pos m (by omega) ((v + t₀) / 2)
  have ha : (((2 * (m : ℝ) + 1 : ℝ) : ℂ) / 2) =
      (((m : ℝ) + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  unfold plattNegativeGammaWindow plattGammaWindow
  rw [ha]
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hg (Real.exp_pos
      (Real.pi * (v + t₀) / 4 - v ^ 2 / (2 * h ^ 2))).le)
    (pow_nonneg (norm_nonneg
      (((2 * (m : ℝ) + 3 / 2 : ℝ) : ℂ) - (v : ℂ) * Complex.I)) k)
  simpa only [mul_assoc] using hb

/-- The negative-line norm integrand is genuinely integrable for a positive window width. -/
theorem integrable_plattNegativeGammaWindow (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) :
    Integrable (plattNegativeGammaWindow m k t₀ h) := by
  apply ((integrable_plattGammaWindow m k hm ht₀ hh).const_mul
    (plattNegativeGammaFactor m)).mono'
    (continuous_plattNegativeGammaWindow m k t₀ h).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro v
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ plattNegativeGammaWindow m k t₀ h v by
    unfold plattNegativeGammaWindow
    positivity)]
  exact plattNegativeGammaWindow_le m k t₀ h v

/-- The negative-line scalar retains its full frequency normalization. -/
def plattNegativeScalarC (m k : ℕ) (t₀ h : ℝ) : ℝ :=
  (2 * Real.pi) ^ k * ∫ v : ℝ, plattNegativeGammaWindow m k t₀ h v

/-- The opposite-line comparison transports to the actual integrals with the same correction. -/
theorem plattNegativeScalarC_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) :
    plattNegativeScalarC m k t₀ h ≤ plattNegativeGammaFactor m * plattScalarC m k t₀ h := by
  have hi := integral_mono (integrable_plattNegativeGammaWindow m k hm ht₀ hh)
    ((integrable_plattGammaWindow m k hm ht₀ hh).const_mul (plattNegativeGammaFactor m))
    (plattNegativeGammaWindow_le m k t₀ h)
  rw [integral_const_mul] at hi
  simpa only [plattNegativeScalarC, plattScalarC, mul_left_comm] using
    mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (2 * Real.pi) ^ k)

/-- The earlier finite Gaussian-moment formula bounds the corrected negative-line scalar. -/
theorem plattNegativeScalarC_le_majorant (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) :
    plattNegativeScalarC m k t₀ h ≤
      plattNegativeGammaFactor m * plattScalarCMajorant m k t₀ h :=
  (plattNegativeScalarC_le m k hm ht₀ hh).trans
    (mul_le_mul_of_nonneg_left (plattScalarC_le_majorant m k hm ht₀ hh)
      (plattNegativeGammaFactor_nonneg m))

end

end PrimeFactorUnimodality
