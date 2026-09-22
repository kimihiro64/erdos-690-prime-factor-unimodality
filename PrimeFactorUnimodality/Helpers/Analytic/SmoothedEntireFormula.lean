import Mathlib.Analysis.Analytic.Uniqueness
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedExplicitFormula
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedPairedEvaluation
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedPrimeEntire

/-! # Analytic continuation of the smoothed explicit formula

Both zero sums are grouped into entire paired Laplace contributions.
The prime sum is entire because its smoothing weight has finite support.
The proved contour formula on `Re(s)>1` therefore extends by the identity
theorem to every complex parameter, including xi zeros and the point one.
No continuation hypothesis or assertion about zero locations is assumed.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Set Filter
open scoped Topology

variable {f : ℝ → ℝ} {g h : ℝ → ℂ} {d M : ℝ}
  (hd : 0 ≤ d) (hM : 0 ≤ M)
  (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
  (hh : ContinuousOn h (Icc 0 d))
  (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt (fun u => (f u : ℂ)) (g u) u)
  (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
  (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
  (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M) (htail : ∀ u, d < u → f u = 0)

include hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound htail

private theorem smoothed_paired_formula_right {s : ℂ} (hs : 1 < s.re) :
    smoothedVonMangoldt f s = finiteLaplace (fun u => (f u : ℂ)) d (s - 1) -
      smoothedXiPairedSum (fun u => (f u : ℂ)) d s -
      smoothedGammaPairedSum (fun u => (f u : ℂ)) d s - (f 0 : ℂ) *
        (logDeriv riemannXi 0 + ((Real.log Real.pi : ℂ) + Real.eulerMascheroniConstant) / 2) := by
  have hfc : ContinuousOn (fun u => (f u : ℂ)) (Icc 0 d) :=
    Complex.continuous_ofReal.comp_continuousOn hf
  have hfdc : (f d : ℂ) = 0 := by rw [hfd]; rfl
  have hraw := smoothedVonMangoldt_explicitFormula_of_one_lt_re hd hM hf hg hh
    hfg hgh hfd hg₀ hgd hbound htail hs
  have hxi := smoothedXiPairedSum_sub_logDeriv_eq_remainders hd hM hfc hg hh
    hfg hgh hfdc hg₀ hgd hbound (riemannXi_ne_zero_of_one_lt_re hs)
  have hgamma := smoothedGammaPairedSum_add_digamma_eq_remainders hd hM hfc hg hh
    hfg hgh hfdc hg₀ hgd hbound (zero_lt_one.trans hs)
  have hlog := neg_logDeriv_riemannZeta_eq_xi hs
  linear_combination hraw + (f 0 : ℂ) * hlog + hxi + hgamma

/-- The full paired complex explicit formula holds on the entire complex plane. -/
theorem smoothedVonMangoldt_entire_explicitFormula (s : ℂ) :
    smoothedVonMangoldt f s = finiteLaplace (fun u => (f u : ℂ)) d (s - 1) -
      smoothedXiPairedSum (fun u => (f u : ℂ)) d s -
      smoothedGammaPairedSum (fun u => (f u : ℂ)) d s - (f 0 : ℂ) *
        (logDeriv riemannXi 0 + ((Real.log Real.pi : ℂ) + Real.eulerMascheroniConstant) / 2) := by
  have hfc : ContinuousOn (fun u => (f u : ℂ)) (Icc 0 d) :=
    Complex.continuous_ofReal.comp_continuousOn hf
  have hfc' : ContinuousOn (fun u => (f u : ℂ)) (uIcc 0 d) := by
    simpa only [uIcc_of_le hd] using hfc
  have hfdc : (f d : ℂ) = 0 := by rw [hfd]; rfl
  let rhs : ℂ → ℂ := fun s => finiteLaplace (fun u => (f u : ℂ)) d (s - 1) -
      smoothedXiPairedSum (fun u => (f u : ℂ)) d s -
      smoothedGammaPairedSum (fun u => (f u : ℂ)) d s - (f 0 : ℂ) *
        (logDeriv riemannXi 0 + ((Real.log Real.pi : ℂ) + Real.eulerMascheroniConstant) / 2)
  have hprime := differentiable_smoothedVonMangoldt htail
  have hxi := differentiable_smoothedXiPairedSum hd hM hfc hg hh
    hfg hgh hfdc hg₀ hgd hbound
  have hgamma := differentiable_smoothedGammaPairedSum hd hM hfc hg hh
    hfg hgh hfdc hg₀ hgd hbound
  have hrhs : Differentiable ℂ rhs :=
    ((((differentiable_finiteLaplace hfc').comp (differentiable_id.sub_const 1)).sub
      hxi).sub hgamma).sub_const _
  have heq : smoothedVonMangoldt f =ᶠ[𝓝 (2 : ℂ)] rhs := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with w hw
    exact smoothed_paired_formula_right hd hM hf hg hh hfg hgh hfd hg₀ hgd hbound htail hw
  have hp : AnalyticOnNhd ℂ (smoothedVonMangoldt f) univ := fun z _ => hprime.analyticAt z
  have hr : AnalyticOnNhd ℂ rhs univ := fun z _ => hrhs.analyticAt z
  exact congrFun (hp.eq_of_eventuallyEq hr heq) s

end

end PrimeFactorUnimodality
