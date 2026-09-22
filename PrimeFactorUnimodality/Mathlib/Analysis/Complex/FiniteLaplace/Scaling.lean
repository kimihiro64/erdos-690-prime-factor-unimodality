/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Basic

/-! # Congruence and rescaling of finite Laplace transforms

The transform depends only on the source on its integration interval.
Multiplication by a constant and a nonzero real change of scale have
the exact expected effect, including the oriented integration endpoints.
-/

namespace Complex

noncomputable section

/-- Sources agreeing on the integration interval have equal finite transforms. -/
theorem finiteLaplace_congr {f g : ℝ → ℂ} {d : ℝ}
    (h : Set.EqOn f g (Set.uIcc 0 d)) (s : ℂ) : finiteLaplace f d s = finiteLaplace g d s := by
  unfold finiteLaplace
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp
  rw [h hu]

/-- A constant factor can be pulled out of the finite transform. -/
theorem finiteLaplace_const_mul (f : ℝ → ℂ) (d : ℝ) (s c : ℂ) :
    finiteLaplace (fun u => c * f u) d s = c * finiteLaplace f d s := by
  unfold finiteLaplace
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  ring

/-- A nonzero real rescaling rescales the transform parameter inversely. -/
theorem finiteLaplace_rescale (f : ℝ → ℂ) (d : ℝ) (s : ℂ) {η : ℝ} (hη : η ≠ 0) :
    finiteLaplace (fun u => (η : ℂ) * f (η * u)) (d / η) s =
      finiteLaplace f d (s / (η : ℂ)) := by
  have hηc : (η : ℂ) ≠ 0 := ofReal_ne_zero.mpr hη
  rw [finiteLaplace_const_mul]
  unfold finiteLaplace
  have hphase (u : ℝ) : -s * (u : ℂ) = -(s / (η : ℂ)) * ((η * u : ℝ) : ℂ) := by
    push_cast
    field_simp
  simp_rw [hphase]
  rw [intervalIntegral.integral_comp_mul_left
    (fun v : ℝ => exp (-(s / (η : ℂ)) * (v : ℂ)) * f v) hη]
  simp only [mul_zero, mul_div_cancel₀ _ hη, real_smul, ofReal_inv]
  rw [← mul_assoc, mul_inv_cancel₀ hηc, one_mul]

end

end Complex
