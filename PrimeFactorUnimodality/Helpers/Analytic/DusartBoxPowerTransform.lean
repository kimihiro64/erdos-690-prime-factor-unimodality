import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxComplexTransform
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.Basic
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.ComplexDecay

/-! # Exact box transform of each complex power

For every nonzero complex exponent the endpoint-corrected Laplace atom is
exactly the average of `t^s/s`. The statement keeps the reciprocal term
paired with its transform, so it never separates a divergent zero series.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Set intervalIntegral

/-- Every paired spectral atom is an actual average of the corresponding power. -/
theorem finiteLaplace_dusartBoxWeight_add_inv (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) {s : ℂ} (hs : s ≠ 0) :
    finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-s) +
        1 / s = iteratedBoxAverageComplex h (m + 3) (fun t => (t : ℂ) ^ s / s) x := by
  have hg := (continuousOn_ofReal_cpow_Ici zero_lt_one (s - 1)).mono
    (show Icc 1 (x + (m + 3 : ℕ) * h) ⊆ Ici 1 from fun _ ht => ht.1)
  have hfg (t : ℝ) (ht : t ∈ Icc 1 (x + (m + 3 : ℕ) * h)) :
      HasDerivAt (fun v : ℝ => (v : ℂ) ^ s / s) ((t : ℂ) ^ (s - 1)) t := by
    have hd := (Complex.hasStrictDerivAt_cpow_const (c := s)
      (ofReal_mem_slitPlane.mpr (lt_of_lt_of_le zero_lt_one ht.1))).hasDerivAt
    convert (hd.div_const s).comp_ofReal using 1
    field_simp [hs]
  have he := integral_dusartBoxWeight_mul_complex_deriv_exp m hh hx hg hfg
  have hk (u : ℝ) : (Real.exp u : ℂ) ^ (s - 1) * (Real.exp u : ℂ) =
      Complex.exp (s * (u : ℂ)) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_ne_zero u)),
      ← ofReal_log (Real.exp_pos u).le, Real.log_exp, ofReal_exp, ← Complex.exp_add]
    congr 1
    ring
  simp_rw [hk] at he
  have hl : (∫ u in (0 : ℝ)..dusartBoxSupport m h x,
      (dusartBoxWeight m h x u : ℂ) * Complex.exp (s * (u : ℂ))) =
      finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-s) := by
    simp only [finiteLaplace, neg_neg, mul_comm]
  rw [hl] at he
  simp only [ofReal_one, one_cpow] at he
  rw [iteratedBoxAverageComplex_sub_const_on_Ici hh
    ((continuousOn_ofReal_cpow_Ici zero_lt_one s).div_const s) hx.le] at he
  rw [he]
  ring

end

end PrimeFactorUnimodality
