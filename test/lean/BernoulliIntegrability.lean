import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.Integrability

/-! # Exact interfaces and boundary cases for normalized xi evaluation -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex
open Polynomial MeasureTheory Set

example (k : Nat) : Measurable (bernoulliPeriodic k) := by
  exact Polynomial.measurable_bernoulliPeriodic k

example (k : Nat) :
    Exists fun C : Real => 1 <= C /\
      forall (a : Real) (z : Complex), 0 < a -> z.re < -1 ->
      MeasureTheory.IntegrableOn
        (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)
        (Set.Ioi a) /\
      norm (MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi a))
        (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z)) <=
        C*(-a^(z.re+1)/(z.re+1)) := by
  exact Polynomial.bernoulliPeriodic_cpow_tail_bound k



end

end PrimeFactorUnimodality.Tests
