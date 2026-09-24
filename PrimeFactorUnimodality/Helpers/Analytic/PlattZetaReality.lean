import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaWindow
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.CompletedConjugate

set_option autoImplicit false

/-! # The completed-zeta connection and the exact Fourier symmetry

The base window is a real scalar times completed zeta on the critical line.
Polynomial order `k` changes conjugation by `(-1)^k`; its transform therefore
has equal norms at opposite frequencies even when the window is not real.
-/

open MeasureTheory
open scoped ComplexConjugate FourierTransform

namespace PrimeFactorUnimodality

/-- The square-root pi phase supplies precisely the completed-zeta normalization. -/
theorem plattPiPhase_eq_completed_factor (t₀ : ℝ) (z : ℂ) :
    plattPiPhase t₀ z = ((Real.pi ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
      (Real.pi : ℂ) ^ (-plattZetaArgument t₀ z / 2) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hs : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hl : Complex.log (Real.sqrt Real.pi : ℂ) = Complex.log (Real.pi : ℂ) / 2 := by
    rw [← Complex.ofReal_log (Real.sqrt_nonneg _), Real.log_sqrt Real.pi_pos.le,
      Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_log Real.pi_pos.le]
  rw [plattPiPhase, Complex.ofReal_cpow Real.pi_pos.le,
    Complex.cpow_def_of_ne_zero hs, Complex.cpow_def_of_ne_zero hp,
    Complex.cpow_def_of_ne_zero hp, ← Complex.exp_add, hl]
  congr 1
  simp only [plattZetaArgument, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- The actual window equals completed zeta times its real Gaussian and polynomial factor. -/
theorem plattZetaWindow_eq_completed (k : ℕ) (t₀ h v : ℝ) :
    plattZetaWindow k t₀ h v =
      ((Real.pi ^ (1 / 4 : ℝ) *
        Real.exp (Real.pi * (v + t₀) / 4 - v ^ 2 / (2 * h ^ 2)) : ℝ) : ℂ) *
      completedRiemannZeta (1 / 2 + ((v + t₀ : ℝ) : ℂ) * Complex.I) *
      (((-2 * Real.pi * v : ℝ) : ℂ) * Complex.I) ^ k := by
  have hg : plattZetaArgument t₀ v / 2 =
      (1 / 4 : ℂ) + (((v + t₀) / 2 : ℝ) : ℂ) * Complex.I := by
    unfold plattZetaArgument
    push_cast
    ring
  have hs : (1 / 2 : ℂ) + ((v + t₀ : ℝ) : ℂ) * Complex.I =
      plattZetaArgument t₀ v := by simp [plattZetaArgument]
  rw [hs, completedRiemannZeta_eq_gamma_mul (by simp)]
  simp only [plattZetaWindow, plattWindowKernel, plattPiPhase_eq_completed_factor,
    Complex.Gammaℝ, hg, Complex.ofReal_mul]
  ring

/-- Conjugation retains the parity of the polynomial frequency factor. -/
theorem conj_plattZetaWindow (k : ℕ) (t₀ h v : ℝ) :
    conj (plattZetaWindow k t₀ h v) = (-1 : ℂ) ^ k * plattZetaWindow k t₀ h v := by
  rw [plattZetaWindow_eq_completed]
  simp only [map_mul, map_pow, Complex.conj_ofReal, Complex.conj_I,
    conj_completedRiemannZeta_critical]
  rw [show ((-2 * Real.pi * v : ℝ) : ℂ) * -Complex.I =
    (-1 : ℂ) * (((-2 * Real.pi * v : ℝ) : ℂ) * Complex.I) by ring, mul_pow]
  ring

/-- The base-order window really is real-valued, including signed centers. -/
theorem plattZetaWindow_zero_im (t₀ h v : ℝ) : (plattZetaWindow 0 t₀ h v).im = 0 := by
  have hc := congrArg Complex.im (conj_plattZetaWindow 0 t₀ h v)
  simp only [Complex.conj_im, pow_zero, one_mul] at hc
  linarith

/-- Opposite Fourier frequencies differ by conjugation and the exact parity sign. -/
theorem conj_fourier_plattZetaWindow (k : ℕ) (t₀ h x : ℝ) :
    conj (𝓕 (plattZetaWindow k t₀ h) x) =
      (-1 : ℂ) ^ k * 𝓕 (plattZetaWindow k t₀ h) (-x) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_conj, ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  simp only [map_mul, conj_plattZetaWindow, ← Complex.exp_conj]
  have he : conj (((-2 * Real.pi * v * x : ℝ) : ℂ) * Complex.I) =
      (((-2 * Real.pi * v * -x : ℝ) : ℂ) * Complex.I) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, Complex.ofReal_neg]
    ring
  rw [map_mul] at he
  rw [he]
  ring

/-- The actual transform has symmetric norm at every polynomial order. -/
theorem norm_fourier_plattZetaWindow_neg (k : ℕ) (t₀ h x : ℝ) :
    ‖𝓕 (plattZetaWindow k t₀ h) (-x)‖ = ‖𝓕 (plattZetaWindow k t₀ h) x‖ := by
  have hc := congrArg norm (conj_fourier_plattZetaWindow k t₀ h x)
  simpa only [Complex.norm_conj, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    using hc.symm

end PrimeFactorUnimodality
