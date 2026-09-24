/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Absolute moments of a Gaussian

The substitution `y = x^2` reduces every half-line Gaussian moment to the
Gamma integral. Reflection then evaluates the absolute natural moments on
the whole real line, with integrability supplied independently.
-/

open MeasureTheory Set

namespace Real

/-- A half-line Gaussian moment, including nonintegral exponents above `-1`. -/
theorem integral_rpow_mul_exp_neg_mul_sq_Ioi {b s : ℝ} (hb : 0 < b) (hs : -1 < s) :
    (∫ x : ℝ in Ioi 0, x ^ s * exp (-b * x ^ 2)) =
      (1 / b) ^ ((s + 1) / 2) * Gamma ((s + 1) / 2) / 2 := by
  have h := integral_comp_rpow_Ioi_of_pos
    (g := fun y : ℝ => y ^ ((s + 1) / 2 - 1) * exp (-(b * y)))
    (by norm_num : (0 : ℝ) < 2)
  have heq : (∫ x : ℝ in Ioi 0,
      (2 * x ^ ((2 : ℝ) - 1)) •
        ((x ^ (2 : ℝ)) ^ ((s + 1) / 2 - 1) * exp (-(b * x ^ (2 : ℝ))))) =
      2 * ∫ x : ℝ in Ioi 0, x ^ s * exp (-b * x ^ 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [smul_eq_mul]
    rw [← rpow_mul hx.le, ← mul_assoc, mul_assoc 2, ← rpow_add hx]
    rw [show (2 : ℝ) - 1 + 2 * ((s + 1) / 2 - 1) = s by ring,
      rpow_two, neg_mul]
    ring
  rw [heq, integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hb] at h
  linarith

/-- Every absolute natural moment of a decaying Gaussian is integrable. -/
theorem integrable_abs_pow_mul_exp_neg_mul_sq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => |x| ^ n * exp (-b * x ^ 2)) := by
  have hi := (integrable_rpow_mul_exp_neg_mul_sq hb
    (show (-1 : ℝ) < (n : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) n])).norm
  simpa only [rpow_natCast, norm_mul, norm_pow, norm_eq_abs,
    abs_of_pos (exp_pos _)] using hi

/-- The exact absolute moment of a Gaussian on the real line. -/
theorem integral_abs_pow_mul_exp_neg_mul_sq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, |x| ^ n * exp (-b * x ^ 2)) =
      (1 / b) ^ (((n : ℝ) + 1) / 2) * Gamma (((n : ℝ) + 1) / 2) := by
  let f : ℝ → ℝ := fun x => |x| ^ n * exp (-b * x ^ 2)
  have hhalf : (∫ x in Ioi 0, f x) =
      (1 / b) ^ (((n : ℝ) + 1) / 2) * Gamma (((n : ℝ) + 1) / 2) / 2 := by
    rw [← integral_rpow_mul_exp_neg_mul_sq_Ioi hb
      (show (-1 : ℝ) < (n : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) n])]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [f, abs_of_pos (mem_Ioi.mp hx), rpow_natCast]
  have hreflect : (∫ x in Iic 0, f x) = ∫ x in Ioi 0, f x := by
    calc
      _ = ∫ x in Ioi 0, f (-x) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi 0 f).symm
      _ = _ := setIntegral_congr_fun measurableSet_Ioi (fun x _ => by simp [f])
  rw [← integral_add_compl measurableSet_Ioi
    (integrable_abs_pow_mul_exp_neg_mul_sq n hb), compl_Ioi]
  change (∫ x in Ioi 0, f x) + (∫ x in Iic 0, f x) = _
  rw [hreflect, hhalf]
  ring

/-- The first absolute Gaussian moment is elementary. -/
theorem integral_abs_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, |x| * exp (-b * x ^ 2)) = 1 / b := by
  simpa using integral_abs_pow_mul_exp_neg_mul_sq 1 hb

/-- All higher moments follow by arithmetic from the zeroth and first moments. -/
theorem integral_abs_pow_mul_exp_neg_mul_sq_add_two (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, |x| ^ (n + 2) * exp (-b * x ^ 2)) =
      ((n : ℝ) + 1) / (2 * b) * ∫ x : ℝ, |x| ^ n * exp (-b * x ^ 2) := by
  rw [integral_abs_pow_mul_exp_neg_mul_sq (n + 2) hb,
    integral_abs_pow_mul_exp_neg_mul_sq n hb]
  have he : (((n + 2 : ℕ) : ℝ) + 1) / 2 = ((n : ℝ) + 1) / 2 + 1 := by
    push_cast
    ring
  rw [he, rpow_add (by positivity : 0 < 1 / b), rpow_one,
    Gamma_add_one (by positivity : ((n : ℝ) + 1) / 2 ≠ 0)]
  ring

end Real
