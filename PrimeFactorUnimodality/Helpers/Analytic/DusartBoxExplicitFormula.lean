import Mathlib.Analysis.Calculus.LocalExtr.Basic
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxCutoff
import PrimeFactorUnimodality.Helpers.Analytic.SmoothedEntireFormula

/-! # The actual explicit formula for the additive box cutoff

The cutoff's twice-continuous differentiability, extremal endpoint values,
and compact derivative bound discharge every analytic hypothesis of the
existing entire explicit formula. No RH or zero-location input is needed.
Identifying the arithmetic side with the averaged Chebyshev sum and
estimating the zero contributions are subsequent steps.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real Set

theorem deriv_dusartBoxWeight_zero (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 ≤ x) :
    deriv (dusartBoxWeight m h x) 0 = 0 := by
  have hm : IsLocalMax (dusartBoxWeight m h x) 0 := by
    apply Filter.Eventually.of_forall
    intro u
    rw [dusartBoxWeight_zero m hh hx]
    exact (dusartBoxWeight_mem_Icc m hh x u).2
  exact hm.deriv_eq_zero

theorem deriv_dusartBoxWeight_support (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    deriv (dusartBoxWeight m h x) (dusartBoxSupport m h x) = 0 := by
  have hm : IsLocalMin (dusartBoxWeight m h x) (dusartBoxSupport m h x) := by
    apply Filter.Eventually.of_forall
    intro u
    rw [dusartBoxWeight_eq_zero m hh hx le_rfl]
    exact (dusartBoxWeight_mem_Icc m hh x u).1
  exact hm.deriv_eq_zero

/-- The box weight satisfies the full paired explicit formula at every complex parameter. -/
theorem dusartBoxWeight_entire_explicitFormula (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) (s : ℂ) :
    smoothedVonMangoldt (dusartBoxWeight m h x) s =
      finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (s - 1) -
        smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
          (dusartBoxSupport m h x) s -
        smoothedGammaPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
          (dusartBoxSupport m h x) s -
        (logDeriv riemannXi 0 + ((Real.log Real.pi : ℂ) + Real.eulerMascheroniConstant) / 2) := by
  have hc := contDiff_dusartBoxWeight m hh x
  have hd : ContDiff ℝ 1 (deriv (dusartBoxWeight m h x)) := hc.deriv'
  have he := hd.continuous_deriv (by norm_num)
  have hs := dusartBoxSupport_pos m hh hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn he.continuousOn
    (s := Icc 0 (dusartBoxSupport m h x))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hs.le⟩)
  have hf := smoothedVonMangoldt_entire_explicitFormula
    (f := dusartBoxWeight m h x)
    (g := fun u => Complex.ofReal (deriv (dusartBoxWeight m h x) u))
    (h := fun u => Complex.ofReal (deriv (deriv (dusartBoxWeight m h x)) u))
    hs.le hM0 hc.continuous.continuousOn
    (Complex.continuous_ofReal.comp hd.continuous).continuousOn
    (Complex.continuous_ofReal.comp he).continuousOn
    (fun u _ => ((hc.differentiable (by norm_num)) u).hasDerivAt.ofReal_comp)
    (fun u _ => ((hd.differentiable (by norm_num)) u).hasDerivAt.ofReal_comp)
    (dusartBoxWeight_eq_zero m hh hx0 le_rfl)
    (by simp [deriv_dusartBoxWeight_zero m hh hx.le])
    (by simp [deriv_dusartBoxWeight_support m hh hx0])
    (fun u hu => by simpa only [Complex.norm_real] using hM u hu)
    (fun u hu => dusartBoxWeight_eq_zero m hh hx0 hu.le) s
  simpa only [dusartBoxWeight_zero m hh hx.le, ofReal_one, one_mul] using hf

end

end PrimeFactorUnimodality
