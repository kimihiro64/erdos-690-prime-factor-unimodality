import PrimeFactorUnimodality.Helpers.Analytic.SmoothedEntireFormula
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaBoundary
import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiHadamardConstant

/-! # The real smoothed explicit formula with the actual gamma boundary term

The complete real zero sum is absolutely convergent. Cancellation of the
real Hadamard constant removes the reciprocal corrections from the entire
paired identity. The resulting real formula holds on EVERY `Re(s)>1/2`,
including xi zeros and the point one. Its gamma remainder is the actual
boundary integral, not a supplied error term.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Set

/-- The real explicit formula, with no regularization left in the zero sum. -/
theorem re_smoothedVonMangoldt_explicitFormula
    {f : ℝ → ℝ} {g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt (fun u => (f u : ℂ)) (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M) (htail : ∀ u, d < u → f u = 0)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    (smoothedVonMangoldt f s).re =
      (finiteLaplace (fun u => (f u : ℂ)) d (s - 1)).re -
      (∑' p : RiemannXiDivisorZeroIndex,
        (finiteLaplace (fun u => (f u : ℂ)) d (s - riemannXiDivisorZeroValue p)).re) +
      f 0 * (-(1 / 2 : ℝ) * Real.log Real.pi + (1 / 2 : ℝ) * (digamma (s / 2 + 1)).re) +
      (smoothedGammaRemainder h d s).re := by
  have hfc : ContinuousOn (fun u => (f u : ℂ)) (Icc 0 d) :=
    Complex.continuous_ofReal.comp_continuousOn hf
  have hfdc : (f d : ℂ) = 0 := by rw [hfd]; rfl
  have hpair := summable_smoothedXiPaired hd hM hfc hg hh hfg hgh
    hfdc hg₀ hgd hbound s
  have hfull := summable_re_xi_finiteLaplace hd hM hfc hg hh hfg hgh
    hfdc hg₀ hgd hbound (by simp) s
  have hzeros : (smoothedXiPairedSum (fun u => (f u : ℂ)) d s).re =
      (∑' p : RiemannXiDivisorZeroIndex,
        (finiteLaplace (fun u => (f u : ℂ)) d (s - riemannXiDivisorZeroValue p)).re) -
      f 0 * (logDeriv riemannXi 0).re := by
    rw [smoothedXiPairedSum, re_tsum hpair]
    simp only [add_re, div_eq_mul_inv, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    have hpole : Summable (fun p : RiemannXiDivisorZeroIndex =>
        f 0 * (riemannXiDivisorZeroValue p)⁻¹.re) := by
      simpa only [one_div] using summable_re_xi_divisor_reciprocal.mul_left (f 0)
    have hld := re_logDeriv_riemannXi_zero_eq_neg_tsum_reciprocal
    simp only [one_div] at hld
    rw [hfull.tsum_add hpole, tsum_mul_left, hld]
    ring
  have hid := smoothedVonMangoldt_entire_explicitFormula hd hM hf hg hh
    hfg hgh hfd hg₀ hgd hbound htail s
  have hgamma := smoothedGammaPairedSum_add_digamma_eq_remainders hd hM hfc hg hh
    hfg hgh hfdc hg₀ hgd hbound (s := s) (by linarith)
  have hboundary := smoothedGammaRemainder_eq_neg_trivialZeroSum hd hM hfc hg hh
    hfg hgh hfdc hg₀ hgd hbound hs
  have hr := congrArg Complex.re hid
  have hgammar := congrArg Complex.re hgamma
  have hboundaryr := congrArg Complex.re hboundary
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hr
  rw [hzeros] at hr
  norm_num [add_re, sub_re, neg_re, mul_re, div_eq_mul_inv] at hr hgammar hboundaryr ⊢
  linear_combination hr - hgammar - hboundaryr

end

end PrimeFactorUnimodality
