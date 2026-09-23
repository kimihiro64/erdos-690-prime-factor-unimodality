import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.ZetaFiniteApproximation

/-! # Exact interfaces and boundary cases for normalized xi evaluation -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex
open MeasureTheory Set

example {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s - zetaEulerApprox N s =
      s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) := by
  exact PrimeFactorUnimodality.riemannZeta_sub_eulerApprox hN hs hs1

example {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - zetaEulerApprox N s‖ ≤ ‖s‖ * (N : ℝ) ^ (-s.re) / s.re := by
  exact PrimeFactorUnimodality.norm_riemannZeta_sub_eulerApprox_le hN hs hs1



end

end PrimeFactorUnimodality.Tests
