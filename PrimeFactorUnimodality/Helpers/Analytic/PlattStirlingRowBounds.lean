import PrimeFactorUnimodality.Helpers.Analytic.GammaStirlingInputs
import PrimeFactorUnimodality.Helpers.Analytic.PlattStirlingRows

/-! # One assembler for every compensated Stirling row

The common context enclosure, local elementary-function bounds, exact
rational correction and rounded exponential jointly enclose the genuine
Gamma-window value. No kernel order re-evaluates Gamma independently.
-/

namespace PrimeFactorUnimodality

open Complex

/-- Local row conditions imply the full compensated logarithmic enclosure. -/
theorem PlattStirlingRow.Valid.norm_log_sub_le {c : PlattStirlingContext}
    (hc : c.Valid) {r : PlattStirlingRow} {v : ℚ} (hr : r.Valid c v) :
    ‖plattCompensatedLogApprox c.order c.center c.width v - (r.logInput c v).toComplex‖ ≤
      (r.logError c : ℝ) := by
  rcases hr with ⟨hell, htheta, hshift, _, hcap⟩
  have harg : 0 < (c.argument v).re := by norm_num [PlattStirlingContext.argument]
  have hg := norm_stirlingApprox_sub_rationalInput_le c.order (c.argument v) harg
    r.ell r.theta c.logTwoPi hell htheta hc.2
  have hcap' : ‖(c.argument v).toComplex - 1 / 2‖ ≤ (r.argumentCap : ℝ) := by
    have h := (RationalPoint.normLE_eq_true _ _).mp hcap
    simpa only [RationalPoint.toComplex_sub, RationalPoint.toComplex_ofRat,
      Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  have hnonneg : 0 ≤ (r.ellError : ℝ) / 2 + (r.thetaError : ℝ) := by
    have h1 := (abs_nonneg _).trans hell
    have h2 := (abs_nonneg _).trans htheta
    positivity
  have hg' := hg.trans (add_le_add
    (mul_le_mul_of_nonneg_right hcap' hnonneg) le_rfl)
  have hs : ‖(plattKernelLogShift c.center c.width v : ℂ) - (r.shift : ℂ)‖ ≤
      (r.shiftError : ℝ) := by
    simpa only [← ofReal_ratCast, ← ofReal_sub, norm_real, Real.norm_eq_abs] using hshift
  have he : plattCompensatedLogApprox c.order c.center c.width v -
      (r.logInput c v).toComplex =
      (gammaStirlingApprox c.order (c.argument v).toComplex -
        (gammaStirlingRationalInput c.order (c.argument v) r.ell r.theta c.logTwoPi).toComplex) +
        ((plattKernelLogShift c.center c.width v : ℂ) - (r.shift : ℂ)) := by
    rw [PlattStirlingRow.logInput, RationalPoint.toComplex_add, RationalPoint.toComplex_ofRat,
      plattCompensatedLogApprox, c.toComplex_argument]
    ring
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add hg' hs)).trans_eq (by
    unfold PlattStirlingRow.logError
    push_cast
    rfl)

/-- A valid compact row encloses the true base value with the complete Stirling remainder. -/
theorem PlattStirlingRow.Valid.norm_kernel_zero_sub_le {c : PlattStirlingContext}
    (hc : c.Valid) {r : PlattStirlingRow} {v : ℚ} (hr : r.Valid c v) :
    ‖plattWindowKernel 0 c.center c.width v - r.value.toComplex‖ ≤
      plattStirlingInputError c.order c.center v (r.logInput c v).toComplex
        (r.logError c) r.expError :=
  norm_plattWindowKernel_zero_sub_stirling_le hc.1 c.center c.width v
    (hr.norm_log_sub_le hc) hr.2.2.2.1

/-- All kernel orders reuse the checked base row, retaining power and multiplication errors. -/
theorem PlattStirlingRow.Valid.norm_kernel_sub_le {c : PlattStirlingContext}
    (hc : c.Valid) {r : PlattStirlingRow} {v : ℚ} (hr : r.Valid c v) (k : ℕ)
    {p w : ℂ} {ν ρ : ℝ} (hp : ‖plattKernelPower k v - p‖ ≤ ν)
    (hw : ‖r.value.toComplex * p - w‖ ≤ ρ) :
    ‖plattWindowKernel k c.center c.width v - w‖ ≤
      plattStirlingInputError c.order c.center v (r.logInput c v).toComplex
        (r.logError c) r.expError * (2 * Real.pi * |(v : ℝ)|) ^ k +
          ‖r.value.toComplex‖ * ν + ρ :=
  norm_plattWindowKernel_sub_rounded_power_le k c.center c.width v
    (hr.norm_kernel_zero_sub_le hc) hp hw

end PrimeFactorUnimodality
