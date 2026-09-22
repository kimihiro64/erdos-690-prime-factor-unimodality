import PrimeFactorUnimodality.Helpers.Analytic.KadiriKernelNormalForm
import PrimeFactorUnimodality.Helpers.Analytic.KadiriTransformGap
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Integrals.ExpTrig

/-! # Closed elementary formula for the actual transform gap

Evaluate each term of the common-frequency kernel decomposition by its
proved endpoint formula. The resulting `K(w,theta)` contains no integral
or complex quantity, and includes both `w=0` and `w=1`. It is an exact
evaluation, not an assertion that the signed gap is monotone or positive.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real MeasureTheory

/-- The real elementary endpoint expression for the kernel's exponential transform. -/
def kadiriKernelExpIntegral (θ w : ℝ) : ℝ :=
  (1 + tan θ ^ 2) *
    ((1 + tan θ ^ 2) / 2 * expLinearCosIntegral w (tan θ) (kadiriSupport θ) +
      expLinearIntegral w (kadiriSupport θ) + 2 * expIntegral w (kadiriSupport θ) +
      expCosIntegral w (tan θ) (kadiriSupport θ) +
      kadiriKernelSineCoefficient θ * expSinIntegral w (tan θ) (kadiriSupport θ))

/-- The elementary expression equals the actual transform for every real exponent. -/
theorem integral_kadiriKernel_mul_exp {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π) (w : ℝ) :
    (∫ u in (0 : ℝ)..kadiriSupport θ, kadiriKernel θ u * Real.exp (w * u)) =
      kadiriKernelExpIntegral θ w := by
  let d := kadiriSupport θ
  let b := tan θ
  let A := 1 + b ^ 2
  let c := kadiriKernelSineCoefficient θ
  have hb : w ≠ 0 ∨ b ≠ 0 := Or.inr (kadiriKernel_frequency_ne_zero hθ)
  have he : IntervalIntegrable (fun u : ℝ => Real.exp (w * u)) volume 0 d :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (w * u))).intervalIntegrable _ _
  have hl : IntervalIntegrable (fun u : ℝ => (d - u) * Real.exp (w * u)) volume 0 d :=
    (by fun_prop : Continuous (fun u : ℝ => (d - u) * Real.exp (w * u))).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun u : ℝ => Real.exp (w * u) * cos (b * u)) volume 0 d :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (w * u) * cos (b * u))).intervalIntegrable _ _
  have hs : IntervalIntegrable (fun u : ℝ => Real.exp (w * u) * sin (b * u)) volume 0 d :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (w * u) * sin (b * u))).intervalIntegrable _ _
  have hlc : IntervalIntegrable (fun u : ℝ => (d - u) * (Real.exp (w * u) * cos (b * u)))
      volume 0 d := (by fun_prop : Continuous
        (fun u : ℝ => (d - u) * (Real.exp (w * u) * cos (b * u)))).intervalIntegrable _ _
  calc
    _ = ∫ u in (0 : ℝ)..d, A *
        ((A / 2 * ((d - u) * (Real.exp (w * u) * cos (b * u))) +
          (d - u) * Real.exp (w * u) + 2 * Real.exp (w * u) +
          Real.exp (w * u) * cos (b * u)) + c * (Real.exp (w * u) * sin (b * u))) := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      rw [kadiriKernel_eq_normalForm hθ u]
      dsimp only [A, b, d, c]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add ((((hlc.const_mul (A / 2)).add hl).add
          (he.const_mul 2)).add hc) (hs.const_mul c),
        intervalIntegral.integral_add (((hlc.const_mul (A / 2)).add hl).add
          (he.const_mul 2)) hc,
        intervalIntegral.integral_add ((hlc.const_mul (A / 2)).add hl) (he.const_mul 2),
        intervalIntegral.integral_add (hlc.const_mul (A / 2)) hl]
      simp only [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_exp_eq_expIntegral,
        intervalIntegral.integral_sub_mul_exp_eq_expLinearIntegral,
        intervalIntegral.integral_exp_mul_cos hb, intervalIntegral.integral_exp_mul_sin hb,
        intervalIntegral.integral_sub_mul_exp_mul_cos hb]
      rfl

/-- A closed formula for the gap, with no integral or complex-valued operation. -/
def kadiriTransformGapClosedForm (θ a₀ a₁ w : ℝ) : ℝ :=
  a₁ * kadiriKernelExpIntegral θ (w - 1) - a₀ * kadiriKernelExpIntegral θ w

/-- The actual signed integral equals the closed formula, including both endpoint exponents. -/
theorem kadiriTransformGap_eq_closedForm {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π)
    (a₀ a₁ w : ℝ) :
    kadiriTransformGap θ a₀ a₁ w = kadiriTransformGapClosedForm θ a₀ a₁ w := by
  have hi (x : ℝ) : IntervalIntegrable
      (fun u => kadiriKernel θ u * Real.exp (x * u)) volume 0 (kadiriSupport θ) :=
    ((continuous_kadiriKernel θ).mul (by fun_prop)).intervalIntegrable _ _
  unfold kadiriTransformGapClosedForm
  rw [← integral_kadiriKernel_mul_exp hθ (w - 1), ← integral_kadiriKernel_mul_exp hθ w,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub ((hi (w - 1)).const_mul a₁) ((hi w).const_mul a₀)]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [show (w - 1) * u = -u + w * u by ring, Real.exp_add]
  ring

end

end PrimeFactorUnimodality
