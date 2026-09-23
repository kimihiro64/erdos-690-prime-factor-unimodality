import PrimeFactorUnimodality.Helpers.Analytic.MomentChunkData

/-! # Real-radius moments and exact rational-grid regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open PrimeFactorUnimodality

example {R : IntervalRat}
    (h : residualWithinHalf R = true) {x : ℝ} (hx : x ∈ R) : |x| ≤ (1 / 2 : ℝ) := by
  exact PrimeFactorUnimodality.abs_le_half_of_residualWithinHalf h hx

example : residualWithinHalf ⟨-1 / 2, 1 / 2, by norm_num⟩ = true := by decide +kernel
example : residualWithinHalf ⟨-1 / 2, 3 / 4, by norm_num⟩ = false := by decide +kernel

end

end PrimeFactorUnimodality.Tests
