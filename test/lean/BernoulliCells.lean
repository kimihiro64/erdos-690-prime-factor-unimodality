import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.Cells

/-! # Exact interfaces and boundary cases for normalized xi evaluation -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex
open Polynomial MeasureTheory Set

example (k N : Nat) (z : Complex) :
    intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
      (N : Real) ((N : Real)+1) MeasureTheory.volume =
    intervalIntegral (fun u : Real =>
      Complex.ofReal (bernoulliNormalizedReal k u)*Complex.ofReal ((N : Real)+u)^z)
      0 1 MeasureTheory.volume := by
  exact Polynomial.bernoulliPeriodic_cpow_unit_shift k N z

example {k N : Nat} (hk : 1 <= k) (hN : 0 < N)
    {z : Complex} (hz : z.re < 0) :
    intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
      (N : Real) ((N : Real)+1) MeasureTheory.volume =
    Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
      (Complex.ofReal ((N : Real)+1)^z-Complex.ofReal (N : Real)^z) -
    z*intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1))
      (N : Real) ((N : Real)+1) MeasureTheory.volume := by
  exact Polynomial.bernoulliPeriodic_cpow_cell hk hN hz

example {k N : Nat} (hk : 1 <= k)
    (hN : 0 < N) {z : Complex} (hz : z.re < -1) (M : Nat) :
    intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
      (N : Real) ((N : Real)+(M : Real)) MeasureTheory.volume =
    Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*
      (Complex.ofReal ((N : Real)+(M : Real))^z-Complex.ofReal (N : Real)^z) -
    z*intervalIntegral (fun x : Real =>
      Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1))
      (N : Real) ((N : Real)+(M : Real)) MeasureTheory.volume := by
  exact Polynomial.bernoulliPeriodic_cpow_finite_recursion hk hN hz M



end

end PrimeFactorUnimodality.Tests
