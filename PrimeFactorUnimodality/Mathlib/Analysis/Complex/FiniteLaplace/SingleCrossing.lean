/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.RealDeriv
import PrimeFactorUnimodality.Mathlib.Analysis.Calculus.Deriv.EndpointMinimum
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Differentiability
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Monotonicity

/-! # Endpoint minima for finite exponential transforms of single-crossing sources

For a continuous source on a nonnegative compact interval, nonnegative
before a cut and nonpositive afterwards, derivative nonpositivity of its
exponential transform persists. Thus the transform has no strict interior
minimum. Differentiation reuses the existing complex finite Laplace theorem.
-/

namespace Real

noncomputable section

open MeasureTheory Set

/-- The real finite exponential transform, with the positive exponent convention. -/
def finiteExpTransform (f : ℝ → ℝ) (d w : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..d, exp (w * u) * f u

/-- The derivative multiplies the compactly supported source by its real coordinate. -/
theorem hasDerivAt_finiteExpTransform {f : ℝ → ℝ} {d : ℝ}
    (hf : ContinuousOn f (uIcc 0 d)) (w : ℝ) :
    HasDerivAt (finiteExpTransform f d) (finiteExpTransform (fun u => u * f u) d w) w := by
  have hfc := Complex.continuous_ofReal.comp_continuousOn hf
  have hsource : (fun u : ℝ => -(u : ℂ) * (f u : ℂ)) =
      (fun u : ℝ => ((-u * f u : ℝ) : ℂ)) := by funext u; push_cast; rfl
  have hneg : ContinuousOn (fun u => -u * f u) (uIcc 0 d) :=
    continuous_id.neg.continuousOn.mul hf
  have h := ((Complex.hasDerivAt_finiteLaplace (f := fun u => (f u : ℂ))
    hfc ((-w : ℝ) : ℂ)).real_of_complex).comp w
    (hasDerivAt_id w).neg
  dsimp only [Function.comp_def] at h
  simp only [hsource, Complex.re_finiteLaplace_ofReal hneg, mul_neg_one] at h
  convert! h using 1
  · funext x
    rw [Complex.re_finiteLaplace_ofReal hf]
    simp only [neg_neg, finiteExpTransform]
  · rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [neg_neg]
    ring

/-- A single crossing controls how the signed transform changes under exponential reweighting. -/
theorem finiteExpTransform_le_exp_mul_of_singleCrossing {f : ℝ → ℝ} {d c x y : ℝ}
    (hd : 0 ≤ d) (hf : ContinuousOn f (Icc 0 d))
    (hpos : ∀ u ∈ Icc 0 d, u ≤ c → 0 ≤ f u)
    (hneg : ∀ u ∈ Icc 0 d, c ≤ u → f u ≤ 0) (hxy : x ≤ y) :
    finiteExpTransform f d y ≤ exp ((y - x) * c) * finiteExpTransform f d x := by
  have hi (w : ℝ) : IntervalIntegrable (fun u => exp (w * u) * f u) volume 0 d :=
    ((by fun_prop : Continuous (fun u : ℝ => exp (w * u))).continuousOn.mul
      (by simpa only [uIcc_of_le hd] using hf)).intervalIntegrable
  unfold finiteExpTransform
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hd (hi y) ((hi x).const_mul _)
  intro u hu
  have hid : y * u = (y - x) * u + x * u := by ring
  rw [hid, exp_add, mul_assoc]
  rcases le_total u c with huc | hcu
  · exact mul_le_mul_of_nonneg_right
      (exp_le_exp.mpr (mul_le_mul_of_nonneg_left huc (sub_nonneg.mpr hxy)))
      (mul_nonneg (exp_pos _).le (hpos u hu huc))
  · exact mul_le_mul_of_nonpos_right
      (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcu (sub_nonneg.mpr hxy)))
      (mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (hneg u hu hcu))

/-- A finite exponential transform of a single-crossing source attains its interval minimum
at one of the two endpoints, even when the transform itself is not monotone. -/
theorem min_finiteExpTransform_endpoints_le {f : ℝ → ℝ} {d c l r w : ℝ}
    (hd : 0 ≤ d) (hf : ContinuousOn f (Icc 0 d))
    (hpos : ∀ u ∈ Icc 0 d, u ≤ c → 0 ≤ f u)
    (hneg : ∀ u ∈ Icc 0 d, c ≤ u → f u ≤ 0) (hw : w ∈ Icc l r) :
    min (finiteExpTransform f d l) (finiteExpTransform f d r) ≤ finiteExpTransform f d w := by
  have hf' : ContinuousOn f (uIcc 0 d) := by simpa only [uIcc_of_le hd] using hf
  apply min_endpoints_le_of_deriv_nonpos_persistent (hasDerivAt_finiteExpTransform hf') _ hw
  intro x y hxy hx
  have h := finiteExpTransform_le_exp_mul_of_singleCrossing hd (continuous_id.continuousOn.mul hf)
    (fun u hu huc => mul_nonneg hu.1 (hpos u hu huc))
    (fun u hu hcu => mul_nonpos_of_nonneg_of_nonpos hu.1 (hneg u hu hcu)) hxy
  exact h.trans (mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le hx)

end

end Real
