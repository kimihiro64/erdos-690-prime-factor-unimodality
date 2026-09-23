import PrimeFactorUnimodality.Helpers.Analytic.DigammaHeightBounds
import PrimeFactorUnimodality.Helpers.Analytic.XiGammaContour

/-! # Lower bounds for horizontal Gamma-factor increments

The existing height-uniform digamma estimate and the actual Gamma-log
primitive give a coarse lower bound without numerical quadrature. The same
primitive identifies the Gamma and pi contribution in the xi log modulus.
-/

namespace PrimeFactorUnimodality

open Complex MeasureTheory

/-- The real logarithmic derivative of the xi Gamma factor is bounded below on the right half-plane. -/
theorem neg_two_le_re_xiGammaLogDerivative {s : ℂ} (hs : 0 ≤ s.re) :
    -2 ≤ (xiGammaLogDerivative s).re := by
  have hz : 1 ≤ (s / 2 + 1).re := by simp only [add_re, div_ofNat_re, one_re]; linarith
  have hn : 1 ≤ ‖s / 2 + 1‖ := hz.trans (re_le_norm _)
  have hd := (abs_le.mp
    (abs_re_digamma_sub_log_norm_le_inv_norm (zero_lt_one.trans_le hz))).1
  have hl := Real.log_nonneg hn
  have hi : 2 / ‖s / 2 + 1‖ ≤ 2 :=
    (div_le_iff₀ (zero_lt_one.trans_le hn)).mpr (by linarith)
  have hp2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hp4 := Real.log_pow (2 : ℝ) 2
  have hpi := Real.log_le_log Real.pi_pos Real.pi_lt_four.le
  norm_num at hp2 hp4
  simp only [xiGammaLogDerivative, add_re, mul_re, neg_re, div_ofNat_re, one_re,
    ofReal_re, ofReal_im, mul_zero, sub_zero, neg_im, div_ofNat_im, one_im,
    zero_div, neg_zero, zero_mul]
  linarith

/-- The same analytic Gamma primitive has a uniform horizontal lower increment. -/
theorem xiGammaLog_horizontal_sub_re_ge {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (T : ℝ) :
    -2 * (b - a) ≤ (xiGammaLog ((b : ℂ) + T * I)).re -
      (xiGammaLog ((a : ℂ) + T * I)).re := by
  have hi := intervalIntegrable_xiGammaLogDerivative_horizontal (T := T) ha hab
  have hir : IntervalIntegrable (fun x : ℝ =>
      (xiGammaLogDerivative ((x : ℂ) + T * I)).re) volume a b := ⟨hi.1.re, hi.2.re⟩
  have h := intervalIntegral.integral_mono_on hab intervalIntegrable_const hir
    (f := fun _ => (-2 : ℝ)) (fun x hx =>
      neg_two_le_re_xiGammaLogDerivative (by simpa using (ha.le.trans hx.1)))
  have hre : (∫ x in a..b, (xiGammaLogDerivative ((x : ℂ) + T * I)).re) =
      (∫ x in a..b, xiGammaLogDerivative ((x : ℂ) + T * I)).re :=
    intervalIntegral.intervalIntegral_re hi
  rw [intervalIntegral.integral_const, hre] at h
  have he := congrArg Complex.re (HIntegral_xiGammaLogDerivative_eq ha hab T)
  change (∫ x in a..b, xiGammaLogDerivative ((x : ℂ) + T * I)).re = _ at he
  rw [sub_re] at he
  rw [he] at h
  simpa only [smul_eq_mul, mul_comm] using h

/-- Moving one unit right lowers the real Gamma logarithm by at most two. -/
theorem xiGammaLog_unit_sub_re_ge {s : ℂ} (hs : 0 < s.re) :
    -2 ≤ (xiGammaLog (s + 1)).re - (xiGammaLog s).re := by
  have h := xiGammaLog_horizontal_sub_re_ge hs
    (show s.re ≤ s.re + 1 by linarith) s.im
  rw [add_sub_cancel_left, mul_one] at h
  have he : ((s.re + 1 : ℝ) : ℂ) + s.im * I = s + 1 := by
    push_cast
    rw [add_right_comm, re_add_im]
  rw [he, re_add_im] at h
  exact h

/-- The actual xi product can use the already constructed Gamma logarithm. -/
theorem riemannXi_eq_pole_mul_exp_xiGammaLog {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s = (s - 1) * exp (xiGammaLog s) * riemannZeta s := by
  have hg : 0 < (s / 2 + 1).re := by simp only [add_re, div_ofNat_re, one_re]; linarith
  rw [riemannXi_eq_shifted_gamma_product_of_re_pos hs hs1, xiGammaLog, exp_sub,
    exp_gammaRightLog hg]
  simp only [div_eq_mul_inv, ← exp_neg, neg_mul]
  ring

/-- The logarithmic modulus separates the actual pole, Gamma and zeta factors at nonzeros. -/
theorem log_norm_riemannXi_eq_pole_gamma_zeta {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) (hxi : riemannXi s ≠ 0) :
    Real.log ‖riemannXi s‖ = Real.log ‖s - 1‖ + (xiGammaLog s).re +
      Real.log ‖riemannZeta s‖ := by
  have hz : riemannZeta s ≠ 0 := by
    intro he
    exact hxi ((riemannXi_eq_zero_iff_riemannZeta_eq_zero hs hs1).mpr he)
  have hp := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs1)
  have hg := norm_ne_zero_iff.mpr (exp_ne_zero (xiGammaLog s))
  rw [riemannXi_eq_pole_mul_exp_xiGammaLog hs hs1, norm_mul, norm_mul,
    Real.log_mul (mul_ne_zero hp hg) (norm_ne_zero_iff.mpr hz), Real.log_mul hp hg,
    norm_exp, Real.log_exp]

end PrimeFactorUnimodality
