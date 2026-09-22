import Mathlib.Analysis.Complex.RealDeriv
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPrimitiveTransform
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageComplex

/-! # Complex primitive evaluation of the box cutoff

The real distribution-transform identity applies to both components of a
complex primitive. All differentiability hypotheses remain local to the
positive arithmetic interval; no regularity across zero is asserted.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set intervalIntegral

theorem integral_dusartBoxWeight_mul_complex_deriv_exp (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) {f g : ℝ → ℂ}
    (hg : ContinuousOn g (Icc 1 (x + (m + 3 : ℕ) * h)))
    (hfg : ∀ t ∈ Icc 1 (x + (m + 3 : ℕ) * h), HasDerivAt f (g t) t) :
    (∫ u in (0 : ℝ)..dusartBoxSupport m h x,
      (dusartBoxWeight m h x u : ℂ) * (g (Real.exp u) * (Real.exp u : ℂ))) =
      iteratedBoxAverageComplex h (m + 3) (fun v => f v - f 1) x := by
  have hd := dusartBoxSupport_pos m hh hx
  have hU : 0 < x + (m + 3 : ℕ) * h :=
    add_pos_of_pos_of_nonneg (lt_trans zero_lt_one hx)
      (mul_nonneg (Nat.cast_nonneg _) hh.le)
  have hmaps : MapsTo Real.exp (uIcc 0 (dusartBoxSupport m h x))
      (Icc 1 (x + (m + 3 : ℕ) * h)) := by
    intro u hu
    rw [uIcc_of_le hd.le] at hu
    refine ⟨Real.one_le_exp_iff.mpr hu.1, ?_⟩
    have he := Real.exp_le_exp.mpr hu.2
    simpa only [dusartBoxSupport, Real.exp_log hU] using he
  have hi : IntervalIntegrable (fun u => (dusartBoxWeight m h x u : ℂ) *
      (g (Real.exp u) * (Real.exp u : ℂ))) volume 0 (dusartBoxSupport m h x) := by
    apply ContinuousOn.intervalIntegrable
    exact (Complex.continuous_ofReal.comp
      (contDiff_dusartBoxWeight m hh x).continuous).continuousOn.mul
        ((hg.comp Real.continuous_exp.continuousOn hmaps).mul
          (Complex.continuous_ofReal.comp Real.continuous_exp).continuousOn)
  apply Complex.ext
  · refine (Complex.reCLM.intervalIntegral_comp_comm hi).symm.trans ?_
    have he := integral_dusartBoxWeight_mul_deriv_exp m hh hx
      (continuous_re.comp_continuousOn hg)
      (fun t ht => Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hfg t ht))
    simpa only [mul_re, ofReal_re, ofReal_im, mul_zero, zero_mul, sub_zero,
      iteratedBoxAverageComplex, sub_re, Complex.reCLM_apply, Function.comp_def] using he
  · refine (Complex.imCLM.intervalIntegral_comp_comm hi).symm.trans ?_
    have he := integral_dusartBoxWeight_mul_deriv_exp m hh hx
      (continuous_im.comp_continuousOn hg)
      (fun t ht => Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hfg t ht))
    simpa only [mul_im, ofReal_re, ofReal_im, mul_zero, zero_mul, add_zero, zero_add,
      iteratedBoxAverageComplex, sub_im, Complex.imCLM_apply, Function.comp_def] using he

end

end PrimeFactorUnimodality
