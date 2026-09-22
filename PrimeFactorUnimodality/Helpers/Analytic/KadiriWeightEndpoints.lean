import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import PrimeFactorUnimodality.Helpers.Analytic.KadiriWeightKernel

/-! # Exact endpoint identities for the paper's smoothing kernel

For every `pi/2 < theta < pi`, the support length is positive, the first
derivative vanishes at zero, and the function and its first two derivatives
vanish at the right endpoint. These symbolic identities are the endpoint
conditions needed by the explicit formula, not numerical approximations.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

variable {θ : ℝ} (hθ : π / 2 < θ ∧ θ < π)

include hθ

private theorem sin_pos : 0 < sin θ :=
  sin_pos_of_pos_of_lt_pi (lt_trans pi_div_two_pos hθ.1) hθ.2

private theorem cos_neg : cos θ < 0 :=
  cos_neg_of_pi_div_two_lt_of_lt hθ.1 (by linarith [pi_pos])

private theorem tan_neg : tan θ < 0 := by
  rw [tan_eq_sin_div_cos]
  exact div_neg_of_pos_of_neg (sin_pos hθ) (cos_neg hθ)

private theorem sec_sq_eq : 1 + tan θ ^ 2 = 1 / cos θ ^ 2 := by
  have hc := (cos_neg hθ).ne
  rw [tan_eq_sin_div_cos]
  field_simp
  nlinarith [sin_sq_add_cos_sq θ]

/-- The support of the unscaled kernel has strictly positive length. -/
theorem kadiriSupport_pos : 0 < kadiriSupport θ := by
  unfold kadiriSupport
  exact div_pos_of_neg_of_neg (by nlinarith [pi_div_two_pos, hθ.1]) (tan_neg hθ)

private theorem support_mul_tan : kadiriSupport θ * tan θ = -2 * θ := by
  rw [kadiriSupport, div_mul_cancel₀ _ (tan_neg hθ).ne]

private theorem phase_endpoints :
    2 * θ + kadiriSupport θ * tan θ = 0 ∧ θ + kadiriSupport θ * tan θ = -θ := by
  rw [support_mul_tan hθ]
  constructor <;> ring

/-- The kernel has the exact endpoint value denoted `g_1(theta)` in the paper. -/
theorem kadiriKernel_zero :
    kadiriKernel θ 0 = (1 + tan θ ^ 2) * (3 - θ * tan θ - 3 * θ / tan θ) := by
  have hs := (sin_pos hθ).ne'
  have hc := (cos_neg hθ).ne
  have hs2 : sin (2 * θ) ≠ 0 := by
    rw [sin_two_mul]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hs) hc
  simp only [kadiriKernel, zero_mul, cos_zero, mul_one, sub_zero, add_zero,
    div_self hs2, div_self hs]
  unfold kadiriSupport
  field_simp [(tan_neg hθ).ne]
  ring

/-- The paper's endpoint value is strictly positive, so the weight is nontrivial. -/
theorem kadiriKernel_zero_pos : 0 < kadiriKernel θ 0 := by
  have ht : 0 < θ := pi_div_two_pos.trans hθ.1
  have hp := mul_neg_of_pos_of_neg ht (tan_neg hθ)
  have hq := div_neg_of_pos_of_neg (show 0 < 3 * θ by positivity) (tan_neg hθ)
  rw [kadiriKernel_zero hθ]
  exact mul_pos (by positivity) (by linarith)

/-- The kernel vanishes exactly at its right endpoint. -/
theorem kadiriKernel_support : kadiriKernel θ (kadiriSupport θ) = 0 := by
  have hs := (sin_pos hθ).ne'
  rw [kadiriKernel, (phase_endpoints hθ).1, (phase_endpoints hθ).2]
  simp [hs]

/-- The first derivative at zero vanishes, as required by two integrations by parts. -/
theorem kadiriKernel₁_zero : kadiriKernel₁ θ 0 = 0 := by
  have hs := (sin_pos hθ).ne'
  have hc := (cos_neg hθ).ne
  simp only [kadiriKernel₁, zero_mul, sin_zero, cos_zero, mul_one, mul_zero,
    sub_zero, add_zero]
  rw [sec_sq_eq hθ, tan_eq_sin_div_cos, sin_two_mul, cos_two_mul]
  field_simp
  ring

/-- The first derivative vanishes at the right endpoint. -/
theorem kadiriKernel₁_support : kadiriKernel₁ θ (kadiriSupport θ) = 0 := by
  have hs := (sin_pos hθ).ne'
  have hc := (cos_neg hθ).ne
  rw [kadiriKernel₁, (phase_endpoints hθ).1, (phase_endpoints hθ).2, support_mul_tan hθ]
  simp only [sub_self, zero_div, zero_mul, sub_zero, cos_zero, mul_one, Real.cos_neg]
  rw [show -2 * θ = -(2 * θ) by ring, Real.cos_neg,
    sec_sq_eq hθ, tan_eq_sin_div_cos, sin_two_mul, cos_two_mul]
  field_simp
  ring

/-- The second derivative also vanishes at the right endpoint. -/
theorem kadiriKernel₂_support : kadiriKernel₂ θ (kadiriSupport θ) = 0 := by
  have hs := (sin_pos hθ).ne'
  have hc := (cos_neg hθ).ne
  rw [kadiriKernel₂, (phase_endpoints hθ).1, (phase_endpoints hθ).2, support_mul_tan hθ]
  simp only [sub_self, zero_div, zero_mul, sub_zero, sin_zero, mul_zero, zero_div, add_zero,
    show -2 * θ = -(2 * θ) by ring, Real.sin_neg]
  rw [sec_sq_eq hθ, tan_eq_sin_div_cos, sin_two_mul]
  field_simp
  ring

omit hθ in
/-- The exact rational parameter selected by Mossinghoff and Trudgian is admissible. -/
theorem mossinghoffTrudgian_theta_mem : π / 2 < (185573 / 100000 : ℝ) ∧
    (185573 / 100000 : ℝ) < π := by
  constructor <;> nlinarith [pi_lt_d2, pi_gt_three]

end

end PrimeFactorUnimodality
