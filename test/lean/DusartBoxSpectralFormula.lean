import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxSpectralFormula

/-! # Exact box-transform and spectral-estimate regressions

Check the discontinuous order-zero step, exact endpoint corrections,
nonreal and negative exponents, finite multiplicity-counted selections,
absolute summability, and the full averaged Chebyshev error.
-/

namespace PrimeFactorUnimodality.Tests

open Complex Set intervalIntegral

example (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, dusartUnitStep (a - t) * g t) = 0 := by
  simpa using integral_dusartUnitStep_mul g le_rfl hab

example {h a b x : ℝ} (hh : 0 < h) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b))
    (hax : a ≤ x) (hxb : x ≤ b) :
    (∫ t in a..b, iteratedBoxAverage h 0 dusartUnitStep (x - t) * g t) =
      ∫ t in a..x, g t := integral_dusartStepAverage_mul 0 hh hg hax (by simpa using hxb)

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) {s : ℂ} (hs : s ≠ 0) :
    finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-s) +
      1 / s = iteratedBoxAverageComplex h (m + 3) (fun t => (t : ℂ) ^ s / s) x :=
  finiteLaplace_dusartBoxWeight_add_inv m hh hx hs

example {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    finiteLaplace (fun u => (dusartBoxWeight 0 h x u : ℂ)) (dusartBoxSupport 0 h x) (-I) +
      1 / I = iteratedBoxAverageComplex h 3 (fun t => (t : ℂ) ^ I / I) x :=
  finiteLaplace_dusartBoxWeight_add_inv 0 hh hx I_ne_zero

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) 2 -
      1 / 2 = iteratedBoxAverageComplex h (m + 3) (fun t => (t : ℂ) ^ (-2 : ℂ) / (-2)) x := by
  simpa [sub_eq_add_neg] using
    finiteLaplace_dusartBoxWeight_add_inv m hh hx (s := -2) (by norm_num)

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-1) =
      (x : ℂ) + (m + 3 : ℕ) * (h : ℂ) / 2 - 1 :=
  finiteLaplace_dusartBoxWeight_neg_one m hh hx

example (m : ℕ) {h x δ : ℝ} (hh : 0 < h) (hx : 1 < x) (hδ : 0 ≤ δ)
    (S : Finset RiemannXiDivisorZeroIndex)
    (hgap : ∀ p ∈ S, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    ‖∑ p ∈ S, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x‖ ≤
      ((x + (m + 3 : ℕ) * h) * Real.exp (-δ * Real.log x)) *
        ∑ p ∈ S, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖ :=
  norm_sum_dusartBox_xi_power_average_le m hh hx hδ S hgap

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x) :=
  summable_dusartBox_xi_power_average m hh hx

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    (dusartPsiAverageError (m + 3) h x : ℂ) =
      -(∑' p : RiemannXiDivisorZeroIndex,
        iteratedBoxAverageComplex h (m + 3)
          (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x) -
        smoothedGammaPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
          (dusartBoxSupport m h x) 0 -
        (logDeriv riemannXi 0 + ((Real.log Real.pi : ℂ) + Real.eulerMascheroniConstant) / 2) - 1 :=
  dusartPsiAverageError_eq_spectral m hh hx

end PrimeFactorUnimodality.Tests
