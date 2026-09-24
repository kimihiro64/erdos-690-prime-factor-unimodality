import PrimeFactorUnimodality.Helpers.Analytic.XiCardinalSignIntervals

/-! # Checked cardinal phase selection and complete zeta margins -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open Complex LeanCert.Core Fourier XiGridSignData

def cardinalRows : RationalGridRows :=
  ⟨[0], fun _ _ => ⟨2, 0⟩, 0,
    ⟨fun n => Vector.replicate (2 ^ (n + 1)) ⟨1, 0⟩, fun _ => 0⟩,
    fun _ => .leaf ⟨2, 0⟩ (1 / 4)⟩
def cardinalSample : XiGridSignData := ⟨⟨0, 0, ⟨3, 0⟩, 0⟩, 0, 0, 0, 0, 1, 0, true⟩
def cardinalPi : IntervalRat := ⟨3, 4, by norm_num⟩

example : cardinalSample.checkCardinalMargin cardinalRows 1 cardinalPi 0 = true := by decide +kernel
example : ({cardinalSample with tailCap := 9 / 2}).checkCardinalMargin
    cardinalRows 1 cardinalPi 0 = true := by decide +kernel
example : ({cardinalSample with
    phase := 7 / 4
    point := {cardinalSample.point with correction := ⟨-2, -5⟩}}).checkCardinalMargin
    cardinalRows 1 cardinalPi 0 = true := by decide +kernel
example : ({cardinalSample with
    phase := 7 / 2
    point := {cardinalSample.point with correction := ⟨-7, 0⟩}}).checkCardinalMargin
    cardinalRows 1 cardinalPi 0 = true := by decide +kernel
example : ({cardinalSample with
    phase := 21 / 4
    point := {cardinalSample.point with correction := ⟨-2, 5⟩}}).checkCardinalMargin
    cardinalRows 1 cardinalPi 0 = true := by decide +kernel
example : ({cardinalSample with phase := -7}).checkCardinalMargin
    cardinalRows 1 cardinalPi 0 = true := by decide +kernel
example : ({cardinalSample with
    phase := 7 / 4
    positive := false
    point := {cardinalSample.point with correction := ⟨-2, 5⟩}}).checkCardinalMargin
    cardinalRows 1 cardinalPi 0 = true := by decide +kernel

example : ({cardinalSample with phaseError := 7 / 5}).checkCardinalMargin
    cardinalRows 1 cardinalPi 0 = false := by decide +kernel
example : ({cardinalSample with phaseError := -1}).checkCardinalMargin
    cardinalRows 1 cardinalPi 0 = false := by decide +kernel
example : ({cardinalSample with phase := 7000000}).checkCardinalMargin
    cardinalRows 1 cardinalPi 0 = false := by decide +kernel
example : ({cardinalSample with positive := false}).checkCardinalMargin
    cardinalRows 1 cardinalPi 0 = false := by decide +kernel
example : ({cardinalSample with tailCap := 5}).checkCardinalMargin
    cardinalRows 1 cardinalPi 0 = false := by decide +kernel
example : ({cardinalSample with point := {cardinalSample.point with error := 5}}).checkCardinalMargin
    cardinalRows 1 cardinalPi 0 = false := by decide +kernel
example : cardinalSample.checkCardinalMargin cardinalRows 1 cardinalPi 5 = false := by decide +kernel

def tightCardinalPi : IntervalRat :=
  ⟨3141592653589793 / 10 ^ 15, 3141592653589794 / 10 ^ 15, by norm_num⟩
def largeCardinalSample : XiGridSignData :=
  {cardinalSample with
    phase := 1000000001 * 3141592653589793 / (2 * 10 ^ 15)
    point := {cardinalSample.point with correction := ⟨-2, -5⟩}}

example : largeCardinalSample.cardinalQuarter tightCardinalPi = 1000000001 := by decide +kernel
example : largeCardinalSample.checkCardinalMargin cardinalRows 1 tightCardinalPi 0 = true :=
  by decide +kernel
example : ({largeCardinalSample with
    phase := -largeCardinalSample.phase
    positive := false}).checkCardinalMargin cardinalRows 1 tightCardinalPi 0 = true :=
  by decide +kernel

example (s : XiGridSignData) (r : RationalGridRows) (degree : ℕ)
    {P : IntervalRat} (hpi : Real.pi ∈ P) (sharedCap : ℚ) {θ : ℝ}
    (hθ : |θ - (s.phase : ℝ)| ≤ 1 / 10 + (s.phaseError : ℝ))
    (h : s.checkCardinalMargin r degree P sharedCap = true) :
    |θ - (s.cardinalQuarter P : ℝ) * Real.pi / 2| < Real.pi / 2 :=
  s.cardinal_phase_of_check r degree hpi sharedCap hθ h

end PrimeFactorUnimodality.Tests
