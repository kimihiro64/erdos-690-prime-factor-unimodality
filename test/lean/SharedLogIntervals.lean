import PrimeFactorUnimodality.Helpers.Analytic.SharedLogIntervals

/-! # Checked elementary xi-phase interfaces and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open PrimeFactorUnimodality.SharedTaylorIntervals

example {c : SharedTaylorIntervals} (hc : c.Prepared)
    {J : IntervalRat} (hJ : 0 < J.lo) {x : ℝ} (hx : x ∈ J) :
    Real.log x ∈ c.logInterval J := by
  exact PrimeFactorUnimodality.SharedTaylorIntervals.mem_logInterval hc hJ hx

example : (prepare 0).logInterval (IntervalRat.singleton 1) = IntervalRat.singleton 0 :=
  by decide +kernel
example {x : ℝ} (hx : x ∈ (⟨1, 2, by norm_num⟩ : IntervalRat)) :
    Real.log x ∈ (prepare 2).logInterval ⟨1, 2, by norm_num⟩ :=
  mem_logInterval (prepare_prepared 2) (by norm_num) hx

end

end PrimeFactorUnimodality.Tests
