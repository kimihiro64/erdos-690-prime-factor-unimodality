import Mathlib.MeasureTheory.Integral.DominatedConvergence
import PrimeFactorUnimodality.Helpers.Analytic.PlattDirichletTail
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaIntegrand

set_option autoImplicit false

/-! # The Dirichlet interchange on a displaced zeta contour

The norm of each term factors into a single integrable Gamma-window norm
and a convergent power of its index. This proves the sum/integral interchange
for the actual zeta integrand, then uses the existing Gamma contour identity
term by term. No expansion of zeta on the critical line is used.
-/

open MeasureTheory
open scoped FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- The pi phase has an exact, height-independent norm on each horizontal line. -/
theorem norm_plattPiPhase (t₀ : ℝ) (z : ℂ) :
    ‖plattPiPhase t₀ z‖ = (Real.sqrt Real.pi) ^ z.im := by
  rw [plattPiPhase, Complex.norm_cpow_eq_rpow_re_of_pos (Real.sqrt_pos.mpr Real.pi_pos)]
  congr 1
  simp

/-- A positive-index term factors in norm even off the original contour. -/
theorem norm_plattDirichletContourTerm (k : ℕ) (t₀ h x : ℝ) {j : ℕ} (hj : 0 < j) (z : ℂ) :
    ‖plattDirichletContourTerm k t₀ h x j z‖ =
      ‖plattContourIntegrand k t₀ h x z‖ * (Real.sqrt Real.pi) ^ z.im *
        (j : ℝ) ^ (z.im - 1 / 2) := by
  rw [plattDirichletContourTerm_eq k t₀ h x hj z, norm_mul, norm_mul,
    norm_plattPiPhase, norm_div, norm_one]
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  rw [show (j : ℂ) = ((j : ℝ) : ℂ) by simp,
    Complex.norm_cpow_eq_rpow_re_of_pos hjr, plattZetaArgument_re,
    show z.im - 1 / 2 = -(1 / 2 - z.im) by ring, Real.rpow_neg hjr.le, one_div]

/-- Exact norm separation on the line of absolute Dirichlet convergence. -/
theorem norm_plattDirichletContourTerm_right (m k : ℕ) (t₀ h x v : ℝ)
    {j : ℕ} (hj : 0 < j) :
    ‖plattDirichletContourTerm k t₀ h x j
        ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)‖ =
      ((Real.sqrt Real.pi) ^ (-plattRightShift m) * (j : ℝ) ^ (-(2 * (m : ℝ) + 1))) *
        ‖plattContourIntegrand k t₀ h x
          ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)‖ := by
  rw [norm_plattDirichletContourTerm k t₀ h x hj]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
  rw [show -plattRightShift m - 1 / 2 = -(2 * (m : ℝ) + 1) by unfold plattRightShift; ring]
  ring

/-- Every individual displaced term is genuinely integrable. -/
theorem integrable_plattDirichletContourTerm_right (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) (j : ℕ) :
    Integrable (fun v : ℝ => plattDirichletContourTerm k t₀ h x j
      ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)) :=
  (integrable_plattContourIntegrand_right m k hm ht₀ hh (x + plattDirichletShift j)).const_mul
    (plattDirichletWeight t₀ j)

/-- The integrals of all term norms form a convergent real series. -/
theorem summable_integral_norm_plattDirichletContourTerm_right (m k : ℕ) (hm : 1 ≤ m)
    (t₀ h x : ℝ) :
    Summable (fun n : ℕ => ∫ v : ℝ, ‖plattDirichletContourTerm k t₀ h x (n + 1)
      ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)‖) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs := (Real.summable_nat_rpow_tail (p := 2 * (m : ℝ) + 1) (by linarith) 0).mul_left
    ((Real.sqrt Real.pi) ^ (-plattRightShift m) * ∫ v : ℝ,
      ‖plattContourIntegrand k t₀ h x
        ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)‖)
  convert hs using 1
  ext n
  simp_rw [norm_plattDirichletContourTerm_right m k t₀ h x _ (by omega : 0 < n + 1)]
  rw [integral_const_mul]
  simp only [Nat.add_zero]
  ring

/-- Each displaced integral is the already defined weighted Fourier term. -/
theorem integral_plattDirichletContourTerm_right (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) (j : ℕ) :
    (∫ v : ℝ, plattDirichletContourTerm k t₀ h x j
      ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)) =
        plattDirichletTerm k t₀ h x j := by
  rw [plattDirichletTerm, fourier_plattWindowKernel_eq_right_integral m k hm ht₀ hh]
  exact integral_const_mul _ _

/-- The actual right-hand zeta integral equals the convergent Gamma Dirichlet series. -/
theorem integral_plattZetaContourIntegrand_right_eq_series (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) :
    (∫ v : ℝ, plattZetaContourIntegrand k t₀ h x
      ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)) =
        plattDirichletSeries k t₀ h x := by
  unfold plattDirichletSeries
  simp_rw [← integral_plattDirichletContourTerm_right m k hm ht₀ hh x]
  rw [integral_tsum_of_summable_integral_norm
    (fun n => integrable_plattDirichletContourTerm_right m k hm ht₀ hh x (n + 1))
    (summable_integral_norm_plattDirichletContourTerm_right m k hm t₀ h x)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  exact plattZetaContourIntegrand_eq_tsum k t₀ h x (by
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add, plattRightShift]
    linarith)

end

end PrimeFactorUnimodality
