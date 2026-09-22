import PrimeFactorUnimodality.Helpers.Analytic.StechkinBasic
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.FiniteLaplace.DirichletIntegral

set_option autoImplicit false

/-! # The prime side of the smoothed explicit formula

Absolute Laplace inversion and a proved interchange identify the weighted
von Mangoldt series with its right-hand contour integral. The original
series at `s` is subtracted with coefficient `f(0)`, leaving precisely the
pole-subtracted transform used in the contour shift. This proves the
inversion and prime-series exchange step of Kadiri section 3.1; the zero
and gamma contributions after contour displacement remain separate work.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- Exact prime-side contour identity, with inversion and interchange discharged internally. -/
theorem smoothedVonMangoldt_sub_logDeriv_eq_integral
    {f : ℝ → ℝ} {g h : ℝ → ℂ} {d M : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc 0 d)) (hg : ContinuousOn g (Icc 0 d))
    (hh : ContinuousOn h (Icc 0 d))
    (hfg : ∀ u ∈ Ioo 0 d, HasDerivAt (fun u => (f u : ℂ)) (g u) u)
    (hgh : ∀ u ∈ Ioo 0 d, HasDerivAt g (h u) u)
    (hfd : f d = 0) (hg₀ : g 0 = 0) (hgd : g d = 0)
    (hbound : ∀ u ∈ Icc 0 d, ‖h u‖ ≤ M) (htail : ∀ u, d < u → f u = 0)
    {s : ℂ} {c : ℝ} (hc : 1 < c) (hcs : c < s.re) :
    smoothedVonMangoldt f s - (f 0 : ℂ) * (-deriv riemannZeta s / riemannZeta s) =
      (1 / (2 * (Real.pi : ℂ))) * (∫ t : ℝ,
        (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
          riemannZeta ((c : ℂ) + (t : ℂ) * I)) *
          (finiteLaplace (fun u => (f u : ℂ)) d (s - ((c : ℂ) + (t : ℂ) * I)) -
            (f 0 : ℂ) / (s - ((c : ℂ) + (t : ℂ) * I)))) := by
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hs : 1 < s.re := hc.trans hcs
  have hfc : ContinuousOn (fun u => (f u : ℂ)) (Icc 0 d) :=
    Complex.continuous_ofReal.comp_continuousOn hf
  have hfdc : (f d : ℂ) = 0 := by rw [hfd]; rfl
  have hidentity := tsum_remainderSource_mul_term_eq_integral hd hM hfc hg hh hfg hgh
    hfdc hg₀ hgd hbound hcs
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))
  have hsource (n : ℕ) : finiteLaplaceRemainderSource (fun u => (f u : ℂ)) d (Real.log n) =
      (f (Real.log n) : ℂ) - (f 0 : ℂ) := by
    by_cases hn : Real.log n ≤ d
    · exact finiteLaplaceRemainderSource_of_mem ⟨Real.log_natCast_nonneg n, hn⟩
    · rw [finiteLaplaceRemainderSource_of_ge hd hfdc (le_of_not_ge hn),
        htail _ (lt_of_not_ge hn), ofReal_zero, zero_sub]
  have hsum : (∑' n : ℕ,
      finiteLaplaceRemainderSource (fun u => (f u : ℂ)) d (Real.log n) * LSeries.term a s n) =
      smoothedVonMangoldt f s - (f 0 : ℂ) * LSeries a s := by
    simp_rw [hsource, sub_mul]
    rw [Summable.tsum_sub (summable_smoothedVonMangoldt htail s)
      ((ArithmeticFunction.LSeriesSummable_vonMangoldt hs).mul_left (f 0 : ℂ)), tsum_mul_left]
    rfl
  change (∑' n : ℕ,
    finiteLaplaceRemainderSource (fun u => (f u : ℂ)) d (Real.log n) * LSeries.term a s n) = _
    at hidentity
  rw [hsum, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs] at hidentity
  rw [hidentity]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hc)]

end

end PrimeFactorUnimodality
