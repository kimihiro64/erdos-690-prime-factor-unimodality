import PrimeFactorUnimodality.Helpers.Analytic.SharedTaylorIntervals

/-! # Shared-moment interfaces and small rational regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset LeanCert.Core
open PrimeFactorUnimodality.SharedTaylorIntervals

variable {degree : ℕ}

example (order : ℕ) : (prepare order).Prepared := by
  exact PrimeFactorUnimodality.SharedTaylorIntervals.prepare_prepared order

example {c : SharedTaylorIntervals} (hc : c.Prepared) {q : ℚ} (hq : 0 < q) :
    Real.log (q : ℝ) ∈ c.log q := by
  exact PrimeFactorUnimodality.SharedTaylorIntervals.mem_log hc hq

example {c : SharedTaylorIntervals} (hc : c.Prepared) {x : ℝ} {J : IntervalRat}
    (hx : x ∈ J) : Real.exp x ∈ c.exp J := by
  exact PrimeFactorUnimodality.SharedTaylorIntervals.mem_exp hc hx

example {c : SharedTaylorIntervals} (hc : c.Prepared) {x : ℝ} {J : IntervalRat}
    (hx : x ∈ J) : Real.sin x ∈ c.sin J := by
  exact PrimeFactorUnimodality.SharedTaylorIntervals.mem_sin hc hx

example {c : SharedTaylorIntervals} (hc : c.Prepared) {x : ℝ} {J : IntervalRat}
    (hx : x ∈ J) : Real.cos x ∈ c.cos J := by
  exact PrimeFactorUnimodality.SharedTaylorIntervals.mem_cos hc hx

example : (prepare 0).log 1 = IntervalRat.singleton 0 := by decide +kernel
example : (prepare 0).exp (IntervalRat.singleton 0) = IntervalRat.singleton 1 := by decide +kernel
example : (prepare 2).sin (IntervalRat.singleton 0) = IntervalRat.singleton 0 := by decide +kernel

end

end PrimeFactorUnimodality.Tests
