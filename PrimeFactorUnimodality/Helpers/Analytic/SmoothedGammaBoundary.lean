import PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaRemainder
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedRealDigammaIntegral

/-! # The paper's gamma boundary remainder as an evaluated pole series

On every `Re(s)>1/2`, the real-digamma integral on the quarter-line plus
the second-derivative remainder at `s` equals the negative trivial-zero
remainder series. The identity includes the exact `1/(2*pi)` factor.
It is proved from absolute Fubini and inversion, not contour displacement.
Its real part is the term `T₂` in Kadiri's equations (7) and (18).
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- Evaluation of the complete gamma boundary term on the required half-plane. -/
theorem smoothedGammaRemainder_eq_neg_trivialZeroSum
    {f g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt f (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    smoothedGammaRemainder h d s =
      -(∑' n : ℕ, (finiteLaplace f d (s - shiftedGammaPole n) -
        f 0 / (s - shiftedGammaPole n))) := by
  have hR (w : ℂ) (hw : w ≠ 0) :
      finiteLaplace f d w - f 0 / w = finiteLaplace h d w / w ^ 2 := by
    rw [finiteLaplace_eq_pole_add hd hf hg hh hfg hgh hfd hg₀ hgd hw, add_sub_cancel_left]
  have hs₀ : s ≠ 0 := by intro heq; norm_num [heq] at hs
  have hne (t : ℝ) : s - ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    norm_num at hre
    linarith
  have hint : (∫ t : ℝ, smoothedGammaIntegrand h d s t) =
      ∫ t : ℝ, (finiteLaplace f d (s - ((1 / 2 : ℂ) + (t : ℂ) * I)) -
        f 0 / (s - ((1 / 2 : ℂ) + (t : ℂ) * I))) *
        ((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) := by
    apply integral_congr_ae
    filter_upwards with t
    rw [hR _ (hne t)]
    unfold smoothedGammaIntegrand
    ring
  have hi := integral_finiteLaplace_mul_re_digamma_eq_remainders hd hM hf hg hh hfg hgh
    hfd hg₀ hgd hbound (c := 1 / 2) (by norm_num) hs
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at hi
  rw [smoothedGammaRemainder, hint, hi, hR s hs₀]
  ring

end

end PrimeFactorUnimodality
