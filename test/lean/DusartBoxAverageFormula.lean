import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxAverageFormula

/-! # Exact arithmetic and explicit-formula regressions for the box average

The identities retain every zero contribution and the constant term.
They assume neither RH nor a numerical zero-free region.
-/

namespace PrimeFactorUnimodality.Tests

open Complex Real Chebyshev intervalIntegral

example : dusartUnitStep 0 = 1 := by norm_num [dusartUnitStep]

example {y : ℝ} {N : ℕ} (hy : 0 ≤ y) (hN : y ≤ N) :
    ψ y = ∑ n ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt n *
      dusartUnitStep (y - n) := psi_eq_sum_dusartUnitStep hy hN

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 0 ≤ x)
    {N : ℕ} (hN : x + (m + 3 : ℕ) * h ≤ N) :
    iteratedBoxAverage h (m + 3) ψ x =
      ∑ n ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt n *
        dusartBoxDistribution m h (x - n) := dusart_psi_average_eq_sum m hh hx hN

example {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    smoothedVonMangoldt (dusartBoxWeight 0 h x) 0 =
      (iteratedBoxAverage h 3 ψ x : ℂ) := smoothedVonMangoldt_box_zero_eq_average 0 hh hx

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    (dusartPsiAverageError (m + 3) h x : ℂ) =
      finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-1) -
        smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
          (dusartBoxSupport m h x) 0 -
        smoothedGammaPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
          (dusartBoxSupport m h x) 0 -
        (logDeriv riemannXi 0 + ((Real.log Real.pi : ℂ) + Real.eulerMascheroniConstant) / 2) -
        (x : ℂ) - (m + 3 : ℕ) * (h : ℂ) / 2 :=
  dusartPsiAverageError_box_explicitFormula m hh hx

end PrimeFactorUnimodality.Tests
