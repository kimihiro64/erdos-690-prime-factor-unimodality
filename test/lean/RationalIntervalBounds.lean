import PrimeFactorUnimodality.Helpers.Analytic.RationalIntervalBounds

/-! # Shared-moment interfaces and small rational regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset LeanCert.Core
open PrimeFactorUnimodality

variable {degree : ℕ}

example {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (q : ℚ) :
    |x - (q : ℝ)| ≤ (intervalPointRadius I q : ℝ) := by
  exact PrimeFactorUnimodality.abs_sub_le_intervalPointRadius hx q

example {I J : IntervalRat} (h : intervalSubset I J = true)
    {x : ℝ} (hx : x ∈ I) : x ∈ J := by
  exact PrimeFactorUnimodality.mem_of_intervalSubset h hx

example : intervalSubset (IntervalRat.singleton 0) ⟨-1, 1, by norm_num⟩ = true := by decide +kernel
example : intervalSubset ⟨-1, 1, by norm_num⟩ (IntervalRat.singleton 0) = false := by decide +kernel

end

end PrimeFactorUnimodality.Tests
