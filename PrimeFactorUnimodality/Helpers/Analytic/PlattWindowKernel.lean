import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.QuarterNorm
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gaussian.AbsoluteMoments

set_option autoImplicit false

/-! # The Gaussian-windowed Gamma kernel on the critical line

The actual complex kernel uses Gamma on real part one quarter. Its uniform
majorant follows from the Beta integral and duplication, with an explicit
constant rather than an assumed numerical estimate. Every natural error
order is covered, and the kernel is genuinely integrable when the window
width is positive.
-/

open MeasureTheory

namespace PrimeFactorUnimodality

noncomputable section

/-- The explicit compensated quarter-line Gamma constant. -/
def plattQuarterGammaConstant : ℝ :=
  Real.sqrt (2 * Real.pi * (Real.Gamma (1 / 4) / Real.Gamma (3 / 4)))

/-- Platt's critical-line kernel `g(v;k)` with its full polynomial frequency factor. -/
def plattWindowKernel (k : ℕ) (t₀ h v : ℝ) : ℂ :=
  Complex.Gamma ((1 / 4 : ℂ) + (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I) *
    (Real.exp (Real.pi * (v + t₀) / 4 - v ^ 2 / (2 * h ^ 2)) : ℂ) *
      (((-2 * Real.pi * v : ℝ) : ℂ) * Complex.I) ^ k

/-- A uniform Gaussian-polynomial bound, valid for either sign of the height. -/
theorem norm_plattWindowKernel_le (k : ℕ) (t₀ h v : ℝ) :
    ‖plattWindowKernel k t₀ h v‖ ≤
      plattQuarterGammaConstant * (2 * Real.pi * |v|) ^ k *
        Real.exp (-v ^ 2 / (2 * h ^ 2)) := by
  have hg := Complex.norm_Gamma_quarter_add_mul_I_mul_exp_le ((v + t₀) / 2)
  have he : Real.pi * ((v + t₀) / 2) / 2 = Real.pi * (v + t₀) / 4 := by ring
  rw [he] at hg
  have hf : ‖(((-2 * Real.pi * v : ℝ) : ℂ) * Complex.I)‖ = 2 * Real.pi * |v| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  unfold plattWindowKernel
  rw [norm_mul, norm_mul, norm_pow, hf, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), sub_eq_add_neg, Real.exp_add]
  have hbound := mul_le_mul_of_nonneg_right hg
    (mul_nonneg (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi * |v|) k)
      (Real.exp_pos (-v ^ 2 / (2 * h ^ 2))).le)
  simpa only [plattQuarterGammaConstant, neg_div, mul_assoc, mul_left_comm, mul_comm]
    using hbound

/-- A completely rational leading constant, with the exact quarter-line value eliminated. -/
theorem norm_plattWindowKernel_le_five (k : ℕ) (t₀ h v : ℝ) :
    ‖plattWindowKernel k t₀ h v‖ ≤
      5 * (2 * Real.pi * |v|) ^ k * Real.exp (-v ^ 2 / (2 * h ^ 2)) := by
  apply (norm_plattWindowKernel_le k t₀ h v).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right Real.sqrt_Gamma_quarter_ratio_le_five (by positivity))
    (Real.exp_pos _).le

/-- The Gamma argument never reaches a pole, so the entire real-height kernel is continuous. -/
theorem continuous_plattWindowKernel (k : ℕ) (t₀ h : ℝ) :
    Continuous (plattWindowKernel k t₀ h) := by
  have hg : Continuous (fun v : ℝ =>
      Complex.Gamma ((1 / 4 : ℂ) + (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    apply (Complex.continuousAt_Gamma _ ?_).comp
      (show ContinuousAt (fun v : ℝ =>
        (1 / 4 : ℂ) + (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I) v by fun_prop)
    intro n hn
    have hr := congrArg Complex.re hn
    norm_num at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact (hg.mul (by fun_prop)).mul (by fun_prop)

private theorem integrable_kernelMajorant (k : ℕ) {h : ℝ} (hh : 0 < h) :
    Integrable (fun v : ℝ => plattQuarterGammaConstant * (2 * Real.pi * |v|) ^ k *
      Real.exp (-v ^ 2 / (2 * h ^ 2))) := by
  have hi := (Real.integrable_abs_pow_mul_exp_neg_mul_sq k
    (by positivity : 0 < 1 / (2 * h ^ 2))).const_mul
      (plattQuarterGammaConstant * (2 * Real.pi) ^ k)
  convert hi using 1
  ext v
  have he : -(1 / (2 * h ^ 2)) * v ^ 2 = -v ^ 2 / (2 * h ^ 2) := by ring
  simp only [mul_pow, he, mul_assoc]

/-- The majorant controls the norm of the actual complex kernel. -/
theorem integrable_plattWindowKernel (k : ℕ) (t₀ : ℝ) {h : ℝ} (hh : 0 < h) :
    Integrable (plattWindowKernel k t₀ h) := by
  exact (integrable_kernelMajorant k hh).mono'
    (continuous_plattWindowKernel k t₀ h).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_plattWindowKernel_le k t₀ h))

/-- The exact Gaussian moment gives a closed bound for the kernel's integral norm. -/
def plattWindowL1Bound (k : ℕ) (h : ℝ) : ℝ :=
  plattQuarterGammaConstant * (2 * Real.pi) ^ k *
    ((2 * h ^ 2) ^ (((k : ℝ) + 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2))

/-- Integrating the full kernel majorant retains every polynomial frequency factor. -/
theorem integral_norm_plattWindowKernel_le (k : ℕ) (t₀ : ℝ) {h : ℝ} (hh : 0 < h) :
    (∫ v : ℝ, ‖plattWindowKernel k t₀ h v‖) ≤ plattWindowL1Bound k h := by
  have he (v : ℝ) :
      plattQuarterGammaConstant * (2 * Real.pi * |v|) ^ k *
          Real.exp (-v ^ 2 / (2 * h ^ 2)) =
        (plattQuarterGammaConstant * (2 * Real.pi) ^ k) *
          (|v| ^ k * Real.exp (-(1 / (2 * h ^ 2)) * v ^ 2)) := by
    have hexp : -(1 / (2 * h ^ 2)) * v ^ 2 = -v ^ 2 / (2 * h ^ 2) := by ring
    simp only [mul_pow, hexp, mul_assoc]
  calc
    _ ≤ ∫ v : ℝ, plattQuarterGammaConstant * (2 * Real.pi * |v|) ^ k *
        Real.exp (-v ^ 2 / (2 * h ^ 2)) :=
      integral_mono (integrable_plattWindowKernel k t₀ hh).norm
        (integrable_kernelMajorant k hh) (norm_plattWindowKernel_le k t₀ h)
    _ = _ := by
      simp_rw [he]
      rw [integral_const_mul, Real.integral_abs_pow_mul_exp_neg_mul_sq k
        (by positivity : 0 < 1 / (2 * h ^ 2)), one_div_one_div]
      rfl

end

end PrimeFactorUnimodality
