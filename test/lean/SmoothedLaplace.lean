import PrimeFactorUnimodality.Helpers.Analytic.SmoothedXiRemainder

set_option autoImplicit false

/-! # Nonzero smoothing and explicit Laplace remainder regressions

On `[0,1]`, `1-3t²+2t³` has value one at zero, value zero at one,
and derivative zero at both endpoints. Its second derivative has norm at
most six. Tests cover the full pole coefficient, bounds on both sides of
the imaginary axis, and convergence over actual xi zeros at every point.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Set

private def weight (t : ℝ) : ℂ := 1 - 3 * (t : ℂ) ^ 2 + 2 * (t : ℂ) ^ 3
private def weight₁ (t : ℝ) : ℂ := -6 * (t : ℂ) + 6 * (t : ℂ) ^ 2
private def weight₂ (t : ℝ) : ℂ := -6 + 12 * (t : ℂ)

private theorem weight_deriv (t : ℝ) : HasDerivAt weight (weight₁ t) t := by
  have ht := (hasDerivAt_id t).ofReal_comp
  have hd := ((hasDerivAt_const t (1 : ℂ)).sub ((ht.pow 2).const_mul 3)).add
    ((ht.pow 3).const_mul 2)
  convert hd using 1
  · funext x
    rfl
  · norm_num [weight₁]
    ring

private theorem weight₁_deriv (t : ℝ) : HasDerivAt weight₁ (weight₂ t) t := by
  have ht := (hasDerivAt_id t).ofReal_comp
  have hd := (ht.const_mul (-6)).add ((ht.pow 2).const_mul 6)
  convert hd using 1
  · funext x
    rfl
  · norm_num [weight₂]
    ring

private theorem weight₂_bound (t : ℝ) (ht : t ∈ Icc 0 1) : ‖weight₂ t‖ ≤ 6 := by
  have heq : weight₂ t = ((-6 + 12 * t : ℝ) : ℂ) := by simp [weight₂]
  rw [heq, norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩

private theorem weight_zero : weight 0 = 1 := by norm_num [weight]

example : weight 0 = 1 := weight_zero

example (s : ℂ) (hs : s ≠ 0) :
    finiteLaplace weight 1 s = 1 / s + finiteLaplace weight₂ 1 s / s ^ 2 := by
  have hid := finiteLaplace_eq_pole_add (f := weight) (g := weight₁) (h := weight₂)
    (by norm_num : (0 : ℝ) ≤ 1)
    (by unfold weight; fun_prop) (by unfold weight₁; fun_prop) (by unfold weight₂; fun_prop)
    (fun t _ => weight_deriv t) (fun t _ => weight₁_deriv t)
    (by norm_num [weight]) (by norm_num [weight₁]) (by norm_num [weight₁]) hs
  simpa only [weight_zero] using hid

example (s : ℂ) (hs : 0 < s.re) :
    ‖finiteLaplace weight 1 s - 1 / s‖ ≤ 6 / (s.re * ‖s‖ ^ 2) := by
  have h := norm_finiteLaplace_sub_pole_le_div_re (f := weight) (g := weight₁) (h := weight₂)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 6)
    (by unfold weight; fun_prop) (by unfold weight₁; fun_prop) (by unfold weight₂; fun_prop)
    (fun t _ => weight_deriv t) (fun t _ => weight₁_deriv t)
    (by norm_num [weight]) (by norm_num [weight₁]) (by norm_num [weight₁]) weight₂_bound hs
  simpa only [weight_zero] using h

example (s : ℂ) (hs : s.re = -1) :
    ‖finiteLaplace weight 1 s - 1 / s‖ ≤ 6 * Real.exp 1 / ‖s‖ ^ 2 := by
  have hs₀ : s ≠ 0 := by intro heq; simp [heq] at hs
  have h := norm_finiteLaplace_sub_pole_le_exp (f := weight) (g := weight₁) (h := weight₂)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 6)
    (by unfold weight; fun_prop) (by unfold weight₁; fun_prop) (by unfold weight₂; fun_prop)
    (fun t _ => weight_deriv t) (fun t _ => weight₁_deriv t)
    (by norm_num [weight]) (by norm_num [weight₁]) (by norm_num [weight₁]) weight₂_bound hs₀
  norm_num only [weight_zero, hs,
    neg_neg, max_eq_right (by norm_num : (0 : ℝ) ≤ 1), mul_one] at h
  exact h

example (s : ℂ) : Summable (fun p : RiemannXiDivisorZeroIndex =>
    (finiteLaplace weight 1 (s - riemannXiDivisorZeroValue p)).re) := by
  exact summable_re_xi_finiteLaplace (g := weight₁) (h := weight₂)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 6)
    (by unfold weight; fun_prop) (by unfold weight₁; fun_prop) (by unfold weight₂; fun_prop)
    (fun t _ => weight_deriv t) (fun t _ => weight₁_deriv t)
    (by norm_num [weight]) (by norm_num [weight₁]) (by norm_num [weight₁]) weight₂_bound
    (by norm_num [weight]) s

end

end PrimeFactorUnimodality.Tests
