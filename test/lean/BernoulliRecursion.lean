import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.NumberTheory.BernoulliPeriodic.Recursion

/-! # Exact interfaces and boundary cases for normalized xi evaluation -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex
open Polynomial MeasureTheory Set

example {k N : Nat} (hk : 1 <= k)
    (hN : 0 < N) {z : Complex} (hz : z.re < -1) :
    MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
      (fun x : Real => Complex.ofReal (bernoulliPeriodic k x)*Complex.ofReal x^z) =
    -Complex.ofReal (bernoulliNormalizedReal (k+1) 0)*Complex.ofReal (N : Real)^z -
    z*MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (N : Real)))
      (fun x : Real => Complex.ofReal (bernoulliPeriodic (k+1) x)*Complex.ofReal x^(z-1)) := by
  exact Polynomial.bernoulliPeriodic_cpow_tail_recursion hk hN hz



end

end PrimeFactorUnimodality.Tests
