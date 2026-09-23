import PrimeFactorUnimodality.Helpers.Analytic.DusartPsiRelativeAverages

/-! # Regression tests for complete Rosser cutoff selection -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real

example (m : ℕ) {s x L U : ℝ}
    (hs : 0 < s) (hx : 0 < x) (hl : 0 < x * (1 - m * s))
    (hleft : |dusartPsiAverageError m (s * x) (x * (1 - m * s))| /
      (x * (1 - m * s)) ≤ L)
    (hright : |dusartPsiAverageError m (s * x) x| / x ≤ U) :
    |ψ x - x| / x ≤ max ((1 - m * s) * L) U + m * s / 2 :=
  dusart_abs_psi_div_le_of_relative_averages m hs hx hl hleft hright

-- The independent-relative assembler includes the identity averaging order.
example {s x L U : ℝ} (hs : 0 < s) (hx : 0 < x)
    (hl : |dusartPsiAverageError 0 (s * x) x| / x ≤ L)
    (hu : |dusartPsiAverageError 0 (s * x) x| / x ≤ U) :
    |ψ x - x| / x ≤ max L U := by
  have he := dusart_abs_psi_div_le_of_relative_averages 0 hs hx
    (by simpa using hx) (by simpa using hl) hu
  simpa using he

end PrimeFactorUnimodality.Tests
