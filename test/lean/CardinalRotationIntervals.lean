import PrimeFactorUnimodality.Helpers.Analytic.CardinalRotationIntervals

/-! # Exact quarter-turn projections, including negative and large periods -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open Complex LeanCert.Core ComplexInterval

example (q : ℤ) {z : ℂ} {J : ComplexInterval} (hz : z ∈ J) :
    (exp (I * (((q : ℝ) * Real.pi / 2 : ℝ) : ℂ)) * z).re ∈ quarterRe q J :=
  mem_quarterRe q hz

def cardinalBox : ComplexInterval := ⟨⟨2, 3, by norm_num⟩, ⟨5, 7, by norm_num⟩⟩

example : quarterRe 0 cardinalBox = cardinalBox.re := by decide +kernel
example : quarterRe 1 cardinalBox = IntervalRat.neg cardinalBox.im := by decide +kernel
example : quarterRe 2 cardinalBox = IntervalRat.neg cardinalBox.re := by decide +kernel
example : quarterRe 3 cardinalBox = cardinalBox.im := by decide +kernel
example : quarterRe (-1) cardinalBox = cardinalBox.im := by decide +kernel
example : quarterRe (-2) cardinalBox = IntervalRat.neg cardinalBox.re := by decide +kernel
example : quarterRe (-3) cardinalBox = IntervalRat.neg cardinalBox.im := by decide +kernel
example : quarterRe (-4) cardinalBox = cardinalBox.re := by decide +kernel
example : quarterRe 1000000001 cardinalBox = IntervalRat.neg cardinalBox.im := by decide +kernel
example : quarterRe (-1000000001) cardinalBox = cardinalBox.im := by decide +kernel

end PrimeFactorUnimodality.Tests
