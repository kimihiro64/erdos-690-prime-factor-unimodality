import PrimeFactorUnimodality.Helpers.Analytic.RadixTwiddleChecks
import PrimeFactorUnimodality.Helpers.Analytic.RationalGridRadiusIntervals

/-! # Real-radius moments and exact rational-grid regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open PrimeFactorUnimodality

example (P : IntervalRat.IntervalRatNonzero)
    (hpi : Real.pi ∈ P.toIntervalRat) (span : ℚ) :
    rationalGridRadius span ∈ rationalGridRadiusInterval P span := by
  exact PrimeFactorUnimodality.mem_rationalGridRadiusInterval P hpi span

def positivePi : IntervalRat.IntervalRatNonzero :=
  ⟨twiddlePi, by norm_num [IntervalRat.containsZero, twiddlePi]⟩
def reciprocalRadius : IntervalRat := rationalGridRadiusInterval positivePi 1

example : rationalGridRadiusInterval positivePi 0 = IntervalRat.singleton 0 := by decide +kernel
example : rationalGridRadius 1 ∈ reciprocalRadius :=
  mem_rationalGridRadiusInterval positivePi pi_mem_twiddlePi 1
example : rationalGridRadius (-1) ∈ rationalGridRadiusInterval positivePi (-1) :=
  mem_rationalGridRadiusInterval positivePi pi_mem_twiddlePi (-1)

end

end PrimeFactorUnimodality.Tests
