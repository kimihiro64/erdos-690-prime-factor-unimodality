import PrimeFactorUnimodality.Helpers.Analytic.BacklundCircleBounds
import PrimeFactorUnimodality.Helpers.Analytic.PlattDirichletInterchange
import PrimeFactorUnimodality.Helpers.Analytic.PlattWindowDerivatives

set_option autoImplicit false

/-! # Integrability of the actual critical-line zeta window

The proved Euler bound controls zeta by a linear function of the height on
the critical line. The previously proved Gamma-window moments absorb this
growth for every polynomial order and every signed center. Thus the Fourier
integral used in the contour argument is an actual absolutely convergent one.
-/

open MeasureTheory
open scoped FourierTransform

namespace PrimeFactorUnimodality

/-- The positive-base pi phase is continuous throughout the complex plane. -/
theorem continuous_plattPiPhase (t₀ : ℝ) : Continuous (plattPiPhase t₀) := by
  unfold plattPiPhase
  simp only [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne')]
  fun_prop

/-- Euler's continuation controls the actual zeta factor for both signs of the window height. -/
theorem norm_riemannZeta_plattArgument_real_le (t₀ v : ℝ) :
    ‖riemannZeta (plattZetaArgument t₀ v)‖ ≤ 4 + 2 * |t₀| + 2 * |v| := by
  have hre : (plattZetaArgument t₀ v).re = 1 / 2 := by simp
  have hne : plattZetaArgument t₀ v ≠ 1 := by
    intro he
    have := congrArg Complex.re he
    rw [hre] at this
    norm_num at this
  have hnorm : ‖plattZetaArgument t₀ v‖ ≤ 1 / 2 + |v + t₀| := by
    simpa [plattZetaArgument, ← Complex.ofReal_add] using
      norm_add_le (1 / 2 : ℂ) (((v : ℂ) + (t₀ : ℂ)) * Complex.I)
  have hden : (1 / 2 : ℝ) ≤ ‖plattZetaArgument t₀ v - 1‖ := by
    have ht := Complex.abs_re_le_norm (plattZetaArgument t₀ v - 1)
    norm_num [hre] at ht
    exact ht
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden
  have hz := norm_riemannZeta_le_euler_one (by rw [hre]; norm_num) hne
  rw [hre] at hz
  have ht : |v + t₀| ≤ |v| + |t₀| := by simpa only [Real.norm_eq_abs] using norm_add_le v t₀
  norm_num at hinv hz
  linarith

/-- The zeta window is continuous: its critical-line argument never meets the pole. -/
theorem continuous_plattZetaWindow (k : ℕ) (t₀ h : ℝ) :
    Continuous (plattZetaWindow k t₀ h) := by
  have hc : Continuous (fun v : ℝ => plattZetaArgument t₀ v) := by
    unfold plattZetaArgument
    fun_prop
  have hz : Continuous (fun v : ℝ => riemannZeta (plattZetaArgument t₀ v)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    apply (differentiableAt_riemannZeta ?_).continuousAt.comp hc.continuousAt
    intro he
    have hr := congrArg Complex.re he
    simp only [plattZetaArgument_re, Complex.ofReal_im, sub_zero, Complex.one_re] at hr
    norm_num at hr
  exact ((continuous_plattWindowKernel k t₀ h).mul
    ((continuous_plattPiPhase t₀).comp Complex.continuous_ofReal)).mul hz

/-- Polynomial Gamma moments absorb the full zeta growth, at any natural order. -/
theorem integrable_plattZetaWindow (k : ℕ) (t₀ : ℝ) {h : ℝ} (hh : 0 < h) :
    Integrable (plattZetaWindow k t₀ h) := by
  have hi₀ := (integrable_plattWindowKernel k t₀ hh).norm.const_mul (4 + 2 * |t₀|)
  have hi₁ := (integrable_pow_smul_plattWindowKernel 1 k t₀ hh).norm.const_mul 2
  apply (hi₀.add hi₁).mono' (continuous_plattZetaWindow k t₀ h).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro v
  change ‖plattZetaWindow k t₀ h v‖ ≤
    (4 + 2 * |t₀|) * ‖plattWindowKernel k t₀ h v‖ +
      2 * ‖v ^ 1 • plattWindowKernel k t₀ h v‖
  rw [plattZetaWindow, norm_mul, norm_mul, norm_plattPiPhase]
  simp only [Complex.ofReal_im, Real.rpow_zero, mul_one, pow_one, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (norm_riemannZeta_plattArgument_real_le t₀ v)
    (norm_nonneg _)).trans_eq (by ring)

/-- Absolute convergence also holds after multiplication by the real Fourier phase. -/
theorem integrable_plattZetaContourIntegrand_real (k : ℕ) (t₀ x : ℝ)
    {h : ℝ} (hh : 0 < h) :
    Integrable (fun v : ℝ => plattZetaContourIntegrand k t₀ h x v) := by
  simp_rw [plattZetaContourIntegrand_real]
  exact (integrable_plattZetaWindow k t₀ hh).bdd_mul (c := 1)
    (by fun_prop) (by
      apply Filter.Eventually.of_forall
      intro v
      rw [Complex.norm_exp]
      simp)

/-- The actual displaced zeta integral is absolutely convergent as well. -/
theorem integrable_plattZetaContourIntegrand_right (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (x : ℝ) :
    Integrable (fun v : ℝ => plattZetaContourIntegrand k t₀ h x
      ((v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I)) := by
  let z : ℝ → ℂ := fun v => (v : ℂ) + ((-plattRightShift m : ℝ) : ℂ) * Complex.I
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr (v : ℝ) : (plattZetaArgument t₀ (z v)).re = 2 * (m : ℝ) + 1 := by
    simp only [plattZetaArgument_re, z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
    unfold plattRightShift
    ring
  have hc : Continuous (fun v => plattZetaArgument t₀ (z v)) := by
    unfold plattZetaArgument z
    fun_prop
  have hz : Continuous (fun v => riemannZeta (plattZetaArgument t₀ (z v))) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    apply (differentiableAt_riemannZeta ?_).continuousAt.comp hc.continuousAt
    intro he
    have hre := congrArg Complex.re he
    rw [hr, Complex.one_re] at hre
    linarith
  have hp : Continuous (fun v => plattPiPhase t₀ (z v)) :=
    (continuous_plattPiPhase t₀).comp (by dsimp [z]; fun_prop)
  have hg := integrable_plattContourIntegrand_right m k hm ht₀ hh x
  apply (hg.norm.const_mul ((Real.sqrt Real.pi) ^ (-plattRightShift m) *
    ‖riemannZeta ((2 * (m : ℝ) + 1 : ℝ) : ℂ)‖)).mono'
      ((hg.aestronglyMeasurable.mul hp.aestronglyMeasurable).mul hz.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro v
  change ‖plattZetaContourIntegrand k t₀ h x (z v)‖ ≤
    ((Real.sqrt Real.pi) ^ (-plattRightShift m) * ‖riemannZeta ((2 * (m : ℝ) + 1 : ℝ) : ℂ)‖) *
      ‖plattContourIntegrand k t₀ h x (z v)‖
  have hb := norm_riemannZeta_le_norm_real (s := plattZetaArgument t₀ (z v))
    (by rw [hr]; linarith)
  rw [hr] at hb
  rw [plattZetaContourIntegrand, norm_mul, norm_mul, norm_plattPiPhase]
  have him : (z v).im = -plattRightShift m := by simp [z]
  rw [him]
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring)

/-- The actual window Fourier transform is the real-line contour integral. -/
theorem fourier_plattZetaWindow_eq_integral (k : ℕ) (t₀ h x : ℝ) :
    𝓕 (plattZetaWindow k t₀ h) x = ∫ v : ℝ, plattZetaContourIntegrand k t₀ h x v := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => by
    dsimp only
    rw [plattZetaContourIntegrand_real]
    rfl)

end PrimeFactorUnimodality
