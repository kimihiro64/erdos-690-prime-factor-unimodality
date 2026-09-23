import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.ZetaEulerApproximation

/-! # Exact interfaces and boundary cases for normalized xi evaluation -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex

example {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (m : ℕ) :
    riemannZeta s - zetaEulerApproxOrder N s m =
      -zetaRisingFactor s (m + 1) * zetaEulerTail N s (m + 1) := by
  exact PrimeFactorUnimodality.riemannZeta_sub_eulerApproxOrder hN hs hs1 m

example {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) (m : ℕ) :
    ‖riemannZeta s - zetaEulerApproxOrder N s m‖ ≤ zetaEulerError N s m := by
  exact PrimeFactorUnimodality.norm_riemannZeta_sub_eulerApproxOrder_le hN hs hs1 m

example (N m : ℕ) {s : ℂ} (hs : 0 < s.re) :
    0 ≤ zetaEulerError N s m := by
  exact PrimeFactorUnimodality.zetaEulerError_nonneg N m hs

example (N : ℕ) (s : ℂ) : zetaEulerApproxOrder N s 0 = zetaEulerApprox N s := by
  simp [zetaEulerApproxOrder]

example (m : ℕ) : 0 ≤ zetaEulerError 1 (1 / 2 : ℂ) m :=
  zetaEulerError_nonneg 1 m (by norm_num)

example {N : ℕ} (hN : 0 < N) (m : ℕ) :
    ‖riemannZeta (1 / 2 : ℂ) - zetaEulerApproxOrder N (1 / 2 : ℂ) m‖ ≤
      zetaEulerError N (1 / 2 : ℂ) m :=
  norm_riemannZeta_sub_eulerApproxOrder_le hN (by norm_num) (by norm_num) m

end

end PrimeFactorUnimodality.Tests
