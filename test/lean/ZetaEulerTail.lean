import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.ZetaEulerTail

/-! # Exact interfaces and boundary cases for normalized xi evaluation -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex
open MeasureTheory Set
open Polynomial

example (s : ℂ) (k : ℕ) :
    zetaRisingFactor s (k + 1) = zetaRisingFactor s k * (s + (k : ℂ)) := by
  exact PrimeFactorUnimodality.zetaRisingFactor_succ s k

example {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s - zetaEulerApprox N s = -s * zetaEulerTail N s 1 := by
  exact PrimeFactorUnimodality.riemannZeta_sub_eulerApprox_eq_tail hN hs hs1

example {N k : ℕ} (hN : 0 < N) (hk : 1 ≤ k)
    {s : ℂ} (hs : 0 < s.re) :
    zetaEulerTail N s k =
      -(bernoulliNormalizedReal (k + 1) 0 : ℂ) * (N : ℂ) ^ (-s - (k : ℂ)) +
        (s + (k : ℂ)) * zetaEulerTail N s (k + 1) := by
  exact PrimeFactorUnimodality.zetaEulerTail_recursion hN hk hs

example {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re)
    (m : ℕ) :
    ‖zetaEulerTail N s (m + 1)‖ ≤ (bernoulliCoeffBound (m + 1) : ℝ) *
      (N : ℝ) ^ (-s.re - (m : ℝ)) / (s.re + (m : ℝ)) := by
  exact PrimeFactorUnimodality.norm_zetaEulerTail_le hN hs m



end

end PrimeFactorUnimodality.Tests
