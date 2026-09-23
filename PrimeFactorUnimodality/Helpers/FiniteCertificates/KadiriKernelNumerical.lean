import LeanCert.Validity.DyadicBounds
import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeightEndpoints

/-! # Kernel-checked scalar bounds for the published smoothing angle

Small expression rows use LeanCert's explicit dyadic correctness theorem,
including its denominator-domain check. All Boolean checks are replayed by
the kernel. The actual kernel and derivative are identified by their proved
endpoint formulas, so no quadrature or rounded analytic identity is used.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real LeanCert.Core LeanCert.Validity

private def angleExpr : Expr := .const (185573 / 100000)
private def tangentExpr : Expr := .div angleExpr.sin angleExpr.cos
private def squareExpr : Expr := .mul tangentExpr tangentExpr
private def factorExpr : Expr := .add (.const 1) squareExpr
private def supportExpr : Expr := .div (.mul (.const (-2)) angleExpr) tangentExpr
private def kernelExpr : Expr := .mul factorExpr
  (.sub (.sub (.const 3) (.mul angleExpr tangentExpr))
    (.div (.mul (.const 3) angleExpr) tangentExpr))
private def derivativeExpr : Expr := .mul (.mul factorExpr squareExpr)
  (.add (.div (.mul factorExpr supportExpr) (.const 2)) (.const 1))

private theorem closed_upper (e : Expr) (c : ℚ)
    (h : checkUpperBoundDyadicChecked e 0 0 (by norm_num) c (-40) 16 = true) :
    Expr.eval (fun _ => (0 : ℝ)) e ≤ (c : ℝ) :=
  verify_upper_bound_dyadic_checked e 0 0 (by norm_num) c (-40) 16
    (by norm_num) h 0 (by norm_num)

private theorem closed_lower (e : Expr) (c : ℚ)
    (h : checkLowerBoundDyadicChecked e 0 0 (by norm_num) c (-40) 16 = true) :
    (c : ℝ) ≤ Expr.eval (fun _ => (0 : ℝ)) e :=
  verify_lower_bound_dyadic_checked e 0 0 (by norm_num) c (-40) 16
    (by norm_num) h 0 (by norm_num)

private theorem supportExpr_eval :
    Expr.eval (fun _ => (0 : ℝ)) supportExpr = kadiriSupport (185573 / 100000) := by
  simp [supportExpr, tangentExpr, angleExpr, Expr.div, Expr.eval,
    kadiriSupport, Real.tan_eq_sin_div_cos, div_eq_mul_inv]

private theorem kernelExpr_eval :
    Expr.eval (fun _ => (0 : ℝ)) kernelExpr = kadiriKernel (185573 / 100000) 0 := by
  rw [kadiriKernel_zero mossinghoffTrudgian_theta_mem]
  simp [kernelExpr, factorExpr, squareExpr, tangentExpr, angleExpr, Expr.div, Expr.eval,
    Real.tan_eq_sin_div_cos, div_eq_mul_inv, pow_two]

private theorem derivativeExpr_eval :
    Expr.eval (fun _ => (0 : ℝ)) derivativeExpr = -kadiriKernel₂ (185573 / 100000) 0 := by
  rw [neg_kadiriKernel₂_zero mossinghoffTrudgian_theta_mem]
  simp only [derivativeExpr, Expr.eval, Expr.div, supportExpr_eval]
  simp [factorExpr, squareExpr, tangentExpr, angleExpr, Expr.div, Expr.eval,
    Real.tan_eq_sin_div_cos, div_eq_mul_inv, pow_two]

/-- The full support is shorter than the chosen exponential-envelope endpoint. -/
theorem mossinghoffTrudgian_support_le : kadiriSupport (185573 / 100000) ≤ (109 / 100 : ℝ) := by
  have h := closed_upper supportExpr (109 / 100) (by decide +kernel)
  simpa only [supportExpr_eval, Rat.cast_div, Rat.cast_ofNat] using h

/-- A rational enclosure of the actual kernel value at zero. -/
theorem mossinghoffTrudgian_kernel_zero_bounds :
    (1387 / 10 : ℝ) ≤ kadiriKernel (185573 / 100000) 0 ∧
      kadiriKernel (185573 / 100000) 0 ≤ (1388 / 10 : ℝ) := by
  have hlo := closed_lower kernelExpr (1387 / 10) (by decide +kernel)
  have hhi := closed_upper kernelExpr (1388 / 10) (by decide +kernel)
  simpa only [kernelExpr_eval, Rat.cast_div, Rat.cast_ofNat] using And.intro hlo hhi

/-- The derivative-maximum moment envelope has an explicit rational coefficient. -/
theorem mossinghoffTrudgian_kernel_second_le :
    -kadiriKernel₂ (185573 / 100000) 0 ≤ (1163 : ℝ) := by
  have h := closed_upper derivativeExpr 1163 (by decide +kernel)
  simpa only [derivativeExpr_eval, Rat.cast_ofNat] using h

/-- The elementary cubic exponential envelope holds at the actual selected endpoint. -/
theorem mossinghoffTrudgian_support_exp_le :
    exp (109 / 100 : ℝ) ≤ 1 + 109 / 100 + (109 / 100) ^ 2 / 2 +
      (109 / 100) ^ 3 / (345 / 100) := by
  have h := closed_upper (.exp (.const (109 / 100))) 3 (by decide +kernel)
  norm_num [Expr.eval] at h
  linarith

end

end PrimeFactorUnimodality
