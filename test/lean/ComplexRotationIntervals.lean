import PrimeFactorUnimodality.Helpers.Analytic.ComplexRotationIntervals

/-! # Full grid-error interfaces and small rational boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open PrimeFactorUnimodality.ComplexInterval

example {P X : IntervalRat} (hpi : Real.pi ∈ P) {x : ℝ} (hx : x ∈ X)
    (turns : ℤ) : x - (turns : ℝ) * (2 * Real.pi) ∈ reducedAngle P X turns := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_reducedAngle hpi hx turns

example {c : SharedTaylorIntervals} (hc : c.Prepared)
    {P X : IntervalRat} (hpi : Real.pi ∈ P) {x : ℝ} (hx : x ∈ X) (turns : ℤ) :
    exp (I * (x : ℂ)) ∈ rotation c P X turns := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_rotation hc hpi hx turns

example {c : SharedTaylorIntervals} (hc : c.Prepared)
    {P X : IntervalRat} (hpi : Real.pi ∈ P) {x : ℝ} (hx : x ∈ X) (turns : ℤ)
    {z : ℂ} {J : ComplexInterval} (hz : z ∈ J) :
    exp (I * (x : ℂ)) * z ∈ (rotation c P X turns).mul J := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_rotated hc hpi hx turns hz

example : rotation (SharedTaylorIntervals.prepare 0) (IntervalRat.singleton 3)
    (IntervalRat.singleton 0) 0 = point ⟨1, 0⟩ := by decide +kernel
example : reducedAngle (IntervalRat.singleton 3) (IntervalRat.singleton 7) 1 =
    IntervalRat.singleton 1 := by decide +kernel
example : reducedAngle (IntervalRat.singleton 3) (IntervalRat.singleton (-7)) (-1) =
    IntervalRat.singleton (-1) := by decide +kernel

end

end PrimeFactorUnimodality.Tests
