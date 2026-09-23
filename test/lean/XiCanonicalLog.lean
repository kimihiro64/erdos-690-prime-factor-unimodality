import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.XiCanonicalLog

/-! # Exact interfaces and boundary cases for the actual logarithmic-ratio chain -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set

example (z : ℂ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      ‖weierstrassFactor 1 (z / riemannXiDivisorZeroValue p) - 1‖) := by
  exact PrimeFactorUnimodality.summable_norm_xi_weierstrass_sub_one z

example (z : ℂ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      Real.log ‖weierstrassFactor 1 (z / riemannXiDivisorZeroValue p)‖) := by
  exact PrimeFactorUnimodality.summable_log_norm_xi_weierstrass z

example {z : ℂ} (hz : riemannXi z ≠ 0)
    (p : RiemannXiDivisorZeroIndex) :
    weierstrassFactor 1 (z / riemannXiDivisorZeroValue p) ≠ 0 := by
  exact PrimeFactorUnimodality.xi_weierstrass_ne_zero hz p

example {z : ℂ} (hz : riemannXi z ≠ 0) :
    Real.log ‖Hadamard.divisorCanonicalProduct 1 riemannXi Set.univ z‖ =
      ∑' p : RiemannXiDivisorZeroIndex,
        Real.log ‖weierstrassFactor 1 (z / riemannXiDivisorZeroValue p)‖ := by
  exact PrimeFactorUnimodality.log_norm_xi_canonicalProduct hz

example : Summable (fun p : RiemannXiDivisorZeroIndex =>
    ‖weierstrassFactor 1 ((0 : ℂ) / riemannXiDivisorZeroValue p) - 1‖) :=
  summable_norm_xi_weierstrass_sub_one 0

example : (∑' p : RiemannXiDivisorZeroIndex,
    Real.log ‖weierstrassFactor 1 ((0 : ℂ) / riemannXiDivisorZeroValue p)‖) = 0 := by simp

example (p : RiemannXiDivisorZeroIndex) : Summable (fun q : RiemannXiDivisorZeroIndex =>
    Real.log ‖weierstrassFactor 1
      (riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue q)‖) :=
  summable_log_norm_xi_weierstrass _

end

end PrimeFactorUnimodality.Tests
