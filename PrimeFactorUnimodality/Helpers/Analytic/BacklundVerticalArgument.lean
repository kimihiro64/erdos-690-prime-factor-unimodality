import PrimeFactorUnimodality.Helpers.Analytic.XiCountingDecomposition
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaEulerLog

/-! # A uniform bound for the vertical Backlund argument

The Euler logarithm of zeta and the principal logarithm of `s-1` give an
analytic logarithm of the entire surrogate on `Re(s)>1`. Integration of
its derivative gives the actual vertical contour integral, whose imaginary
part is bounded by `pi/2 + log(norm(zeta(sigma)))`, independently of height.
The same Euler estimate supplies a quantitative lower bound at Jensen's
centre. No assumption on the counting error or the Riemann hypothesis is used.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- An analytic logarithm of the surrogate on the half-plane to the right of one. -/
def backlundRightLog (s : ℂ) : ℂ := log (s - 1) + riemannZetaEulerLog s

/-- This logarithm exponentiates to the actual surrogate, not only to its modulus. -/
theorem exp_backlundRightLog {s : ℂ} (hs : 1 < s.re) :
    exp (backlundRightLog s) = Backlund.zetaSurrogate s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  simp only [backlundRightLog, exp_add, exp_log (sub_ne_zero.mpr hs1),
    exp_riemannZetaEulerLog hs, Backlund.zetaSurrogate, ite_eq_right hs1]

/-- Its derivative is the exact logarithmic derivative already used by the contour. -/
theorem hasDerivAt_backlundRightLog {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt backlundRightLog (logDeriv Backlund.zetaSurrogate s) s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hslit : s - 1 ∈ slitPlane := Or.inl (by simp only [sub_re, one_re]; linarith)
  have hlog : HasDerivAt (fun z : ℂ => log (z - 1)) (1 / (s - 1)) s := by
    convert! (hasDerivAt_log hslit).comp s ((hasDerivAt_id s).sub_const 1) using 1
    simp
  have he := (differentiableAt_riemannZetaEulerLog hs).hasDerivAt
  rw [deriv_riemannZetaEulerLog hs] at he
  rw [logDeriv_backlundSurrogate_eq hs1 (riemannZeta_ne_zero_of_one_le_re hs.le)]
  convert! hlog.add he using 1

/-- The starting value on the real axis has exactly zero argument. -/
theorem backlundRightLog_ofReal_im {σ : ℝ} (hσ : 1 < σ) :
    (backlundRightLog (σ : ℂ)).im = 0 := by
  simp only [backlundRightLog, add_im, riemannZetaEulerLog_ofReal_im, add_zero, log_im,
    ← ofReal_one, ← ofReal_sub, arg_ofReal_of_nonneg (by linarith : 0 ≤ σ - 1)]

/-- A height-independent bound for the surrogate argument in the right half-plane. -/
theorem abs_im_backlundRightLog_le {s : ℂ} (hs : 1 < s.re) :
    |(backlundRightLog s).im| ≤ Real.pi / 2 + Real.log ‖riemannZeta (s.re : ℂ)‖ := by
  have harg : |arg (s - 1)| ≤ Real.pi / 2 :=
    abs_arg_le_pi_div_two_iff.mpr (by simp only [sub_re, one_re]; linarith)
  simp only [backlundRightLog, add_im, log_im]
  exact (abs_add_le _ _).trans (add_le_add harg (abs_im_riemannZetaEulerLog_le hs))

/-- The vertical contour integral is the increment of this fixed analytic logarithm. -/
theorem VIntegral_backlund_logDeriv_eq {σ : ℝ} (hσ : 1 < σ) (T : ℝ) :
    VIntegral (logDeriv Backlund.zetaSurrogate) σ 0 T =
      backlundRightLog ((σ : ℂ) + T * I) - backlundRightLog (σ : ℂ) := by
  have hd (t : ℝ) :
      HasDerivAt (fun y : ℝ => backlundRightLog ((σ : ℂ) + y * I))
        (I * logDeriv Backlund.zetaSurrogate ((σ : ℂ) + t * I)) t := by
    have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
    have h := (hasDerivAt_backlundRightLog hs).comp (t : ℂ)
      (((hasDerivAt_id (t : ℂ)).mul_const I).const_add (σ : ℂ))
    simpa [mul_comm] using h.comp_ofReal
  have hi := ((continuous_backlund_logDeriv_vertical hσ).intervalIntegrable
    (μ := MeasureTheory.volume) 0 T).const_mul I
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa only [intervalIntegral.integral_const_mul, ofReal_zero, zero_mul, add_zero,
    VIntegral, smul_eq_mul] using h

/-- The previously unbounded vertical term is uniformly bounded at every height. -/
theorem abs_im_VIntegral_backlund_logDeriv_le {σ : ℝ} (hσ : 1 < σ) (T : ℝ) :
    |(VIntegral (logDeriv Backlund.zetaSurrogate) σ 0 T).im| ≤
      Real.pi / 2 + Real.log ‖riemannZeta (σ : ℂ)‖ := by
  rw [VIntegral_backlund_logDeriv_eq hσ, sub_im, backlundRightLog_ofReal_im hσ, sub_zero]
  simpa using abs_im_backlundRightLog_le (s := (σ : ℂ) + T * I) (by simpa using hσ)

/-- Euler's product bounds the centre modulus without a new nonvanishing hypothesis. -/
theorem norm_backlundSurrogate_ge {s : ℂ} (hs : 1 < s.re) :
    ‖s - 1‖ / ‖riemannZeta (s.re : ℂ)‖ ≤ ‖Backlund.zetaSurrogate s‖ := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  simp only [Backlund.zetaSurrogate, ite_eq_right hs1, norm_mul, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_norm_riemannZeta_real_le hs) (norm_nonneg _)

/-- The centre has at least linear growth in the absolute height. -/
theorem abs_height_div_zeta_le_backlundSurrogate {σ : ℝ} (hσ : 1 < σ) (T : ℝ) :
    |T| / ‖riemannZeta (σ : ℂ)‖ ≤ ‖Backlund.zetaSurrogate ((σ : ℂ) + T * I)‖ := by
  have hn : |T| ≤ ‖(σ : ℂ) + T * I - 1‖ := by
    simpa using abs_im_le_norm ((σ : ℂ) + T * I - 1)
  exact (div_le_div_of_nonneg_right hn (norm_nonneg _)).trans
    (by simpa using norm_backlundSurrogate_ge (s := (σ : ℂ) + T * I) (by simpa using hσ))

end

end PrimeFactorUnimodality
