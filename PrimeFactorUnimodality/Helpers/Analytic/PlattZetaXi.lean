import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaReality
import PrimeFactorUnimodality.Helpers.Analytic.XiCriticalLine

set_option autoImplicit false

/-! # Transport from the actual Platt window to xi zero witnesses

The base window is a negative positive-scale multiple of the real xi
restriction. This exact identity transfers genuine window sign changes
to the existing xi divisor machinery, without redefining xi or asserting
any numerical sign. Widths and centers may be arbitrary real numbers.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- The strictly positive normalization relating the base window to xi. -/
def plattZetaXiScale (t₀ h v : ℝ) : ℝ :=
  2 * (Real.pi ^ (1 / 4 : ℝ) *
    Real.exp (Real.pi * (v + t₀) / 4 - v ^ 2 / (2 * h ^ 2))) /
    ((v + t₀) ^ 2 + 1 / 4)

theorem plattZetaXiScale_pos (t₀ h v : ℝ) : 0 < plattZetaXiScale t₀ h v := by
  unfold plattZetaXiScale
  positivity

/-- The precise complex identity, including the negative sign of the xi normalization. -/
theorem plattZetaWindow_zero_eq_xi (t₀ h v : ℝ) :
    plattZetaWindow 0 t₀ h v = -(plattZetaXiScale t₀ h v : ℂ) *
      riemannXi (1 / 2 + ((v + t₀ : ℝ) : ℂ) * Complex.I) := by
  have hs₀ : (1 / 2 : ℂ) + ((v + t₀ : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
  have hs₁ : (1 / 2 : ℂ) + ((v + t₀ : ℝ) : ℂ) * Complex.I ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
  have hp : ((1 / 2 : ℂ) + ((v + t₀ : ℝ) : ℂ) * Complex.I) *
      ((1 / 2 : ℂ) + ((v + t₀ : ℝ) : ℂ) * Complex.I - 1) =
        -(((v + t₀) ^ 2 + 1 / 4 : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
        Complex.add_im, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re,
        Complex.one_im, Complex.I_re, Complex.I_im] <;> ring
  rw [plattZetaWindow_eq_completed, riemannXi_eq_mul_completedRiemannZeta hs₀ hs₁, hp]
  simp only [pow_zero, mul_one, plattZetaXiScale]
  have hd : (((v + t₀) ^ 2 + 1 / 4 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  push_cast at hd ⊢
  field_simp at hd
  replace hd := (div_ne_zero_iff.mp hd).1
  field_simp [hd]

/-- The real restriction is the negative positive-scale xi value at the actual ordinate. -/
theorem neg_re_plattZetaWindow_eq_scaled_xi (t₀ h v : ℝ) :
    -(plattZetaWindow 0 t₀ h v).re = plattZetaXiScale t₀ h v * xiCriticalLineValue (v + t₀) := by
  rw [plattZetaWindow_zero_eq_xi]
  simp [Complex.mul_re, xiCriticalLineValue]

/-- Either strict window sign change transfers to the actual xi restriction. -/
theorem xi_sign_change_of_plattZetaWindow {t₀ h a b : ℝ}
    (hsign : (plattZetaWindow 0 t₀ h a).re * (plattZetaWindow 0 t₀ h b).re < 0) :
    xiCriticalLineValue (a + t₀) * xiCriticalLineValue (b + t₀) < 0 := by
  apply xiCriticalLine_sign_change_of_scaled (plattZetaXiScale_pos t₀ h a)
    (plattZetaXiScale_pos t₀ h b)
  rw [← neg_re_plattZetaWindow_eq_scaled_xi, ← neg_re_plattZetaWindow_eq_scaled_xi, neg_mul_neg]
  exact hsign

/-- Reuse the existing genuine divisor label supplied by a strict window sign change. -/
theorem exists_xi_index_of_plattZetaWindow_sign_change {t₀ h a b : ℝ} (hab : a < b)
    (hsign : (plattZetaWindow 0 t₀ h a).re * (plattZetaWindow 0 t₀ h b).re < 0) :
    ∃ p : RiemannXiDivisorZeroIndex, (riemannXiDivisorZeroValue p).re = 1 / 2 ∧
      (riemannXiDivisorZeroValue p).im ∈ Set.Ioo (a + t₀) (b + t₀) :=
  exists_xi_criticalLine_index_of_sign_change (by linarith)
    (xi_sign_change_of_plattZetaWindow hsign)

end

end PrimeFactorUnimodality
