import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxExplicitFormula
import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPrimeSum
import PrimeFactorUnimodality.Helpers.Analytic.DusartPsiSmoothing

/-! # The unconditional explicit formula for the actual averaged psi error

Identify the box weight's prime side with the iterated Chebyshev average,
then subtract the exact averaged linear main term. Every multiplicity-counted
xi contribution, negative-even contribution, and endpoint constant remains
visible. This is an exact identity, not a numerical error estimate.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real Chebyshev intervalIntegral

/-- The complete averaged Chebyshev error, with no assumed explicit-formula input. -/
theorem dusartPsiAverageError_box_explicitFormula (m : ℕ) {h x : ℝ}
    (hh : 0 < h) (hx : 1 < x) :
    (dusartPsiAverageError (m + 3) h x : ℂ) =
      finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-1) -
        smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
          (dusartBoxSupport m h x) 0 -
        smoothedGammaPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
          (dusartBoxSupport m h x) 0 -
        (logDeriv riemannXi 0 + ((Real.log Real.pi : ℂ) + Real.eulerMascheroniConstant) / 2) -
        (x : ℂ) - (m + 3 : ℕ) * (h : ℂ) / 2 := by
  rw [dusartPsiAverageError, iteratedBoxAverage_sub_id hh psi_mono]
  push_cast
  rw [← smoothedVonMangoldt_box_zero_eq_average m hh (lt_trans zero_lt_one hx),
    dusartBoxWeight_entire_explicitFormula m hh hx]
  norm_num

end

end PrimeFactorUnimodality
