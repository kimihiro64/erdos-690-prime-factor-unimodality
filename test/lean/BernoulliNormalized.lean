import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.Normalized

/-! # Exact interfaces and boundary cases for normalized xi evaluation -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex
open Polynomial MeasureTheory Set

example (k : Nat) :
    derivative (bernoulliNormalized (k+1)) = bernoulliNormalized k := by
  exact Polynomial.derivative_bernoulliNormalized k

example {k : Nat} (hk : Not (k = 1)) :
    (bernoulliNormalized k).eval 1 = (bernoulliNormalized k).eval 0 := by
  exact Polynomial.bernoulliNormalized_one_eq_zero hk

example (k : Nat) (u : Real) :
    HasDerivAt (bernoulliNormalizedReal (k+1)) (bernoulliNormalizedReal k u) u := by
  exact Polynomial.hasDerivAt_bernoulliNormalizedReal k u

example {k : Nat} (hk : Not (k = 1)) :
    bernoulliNormalizedReal k 1 = bernoulliNormalizedReal k 0 := by
  exact Polynomial.bernoulliNormalizedReal_one_eq_zero hk

example (k : Nat) :
    Continuous (bernoulliNormalizedReal k) := by
  exact Polynomial.continuous_bernoulliNormalizedReal k

example {k : Nat} (hk : 1 <= k)
    {a : Real} (ha : 0 < a) {z : Complex} (hz : z.re < 0) :
    intervalIntegral (fun u : Real =>
      Complex.ofReal (bernoulliNormalizedReal k u)*Complex.ofReal (a+u)^z)
      0 1 MeasureTheory.volume =
    Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
      (Complex.ofReal (a+1)^z-Complex.ofReal a^z) -
    z*intervalIntegral (fun u : Real =>
      Complex.ofReal (bernoulliNormalizedReal (k+1) u)*Complex.ofReal (a+u)^(z-1))
      0 1 MeasureTheory.volume := by
  exact Polynomial.bernoulliNormalizedReal_cpow_cell hk ha hz



end

end PrimeFactorUnimodality.Tests
