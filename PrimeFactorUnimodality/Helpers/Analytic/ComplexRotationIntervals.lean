import PrimeFactorUnimodality.Helpers.Analytic.ComplexInterval
import PrimeFactorUnimodality.Helpers.Analytic.SharedTaylorIntervals

/-! # Enclosed unit rotations with exact integer phase reduction

An arbitrary integer period shift is sound for every enclosed real angle.
The shared pi interval is retained in the reduced interval, and the prepared
sine/cosine enclosures include their entire numerical errors.
-/

namespace PrimeFactorUnimodality.ComplexInterval

open Complex LeanCert.Core

/-- Reduce an enclosed angle by an integer number of complete periods. -/
def reducedAngle (P X : IntervalRat) (turns : ℤ) : IntervalRat :=
  IntervalRat.sub X (IntervalRat.scale (2 * turns) P)

/-- The exact shifted angle is enclosed for every period choice. -/
theorem mem_reducedAngle {P X : IntervalRat} (hpi : Real.pi ∈ P) {x : ℝ} (hx : x ∈ X)
    (turns : ℤ) : x - (turns : ℝ) * (2 * Real.pi) ∈ reducedAngle P X turns := by
  have h := IntervalRat.mem_sub hx (IntervalRat.mem_scale (2 * turns) hpi)
  simpa [reducedAngle, mul_assoc, mul_left_comm] using h

/-- Evaluate one unit rotation using shared Taylor constants and the reduced angle. -/
def rotation (c : SharedTaylorIntervals) (P X : IntervalRat) (turns : ℤ) : ComplexInterval :=
  let H := reducedAngle P X turns
  ⟨c.cos H, c.sin H⟩

/-- The full rectangle encloses the actual complex unit rotation. -/
theorem mem_rotation {c : SharedTaylorIntervals} (hc : c.Prepared)
    {P X : IntervalRat} (hpi : Real.pi ∈ P) {x : ℝ} (hx : x ∈ X) (turns : ℤ) :
    exp (I * (x : ℂ)) ∈ rotation c P X turns := by
  have h := mem_reducedAngle hpi hx turns
  have hcos := SharedTaylorIntervals.mem_cos hc h
  have hsin := SharedTaylorIntervals.mem_sin hc h
  rw [Real.cos_sub_int_mul_two_pi] at hcos
  rw [Real.sin_sub_int_mul_two_pi] at hsin
  constructor
  · simpa [rotation, Complex.exp_re] using hcos
  · simpa [rotation, Complex.exp_im] using hsin

/-- Rotate an enclosed complex value without evaluating it again. -/
theorem mem_rotated {c : SharedTaylorIntervals} (hc : c.Prepared)
    {P X : IntervalRat} (hpi : Real.pi ∈ P) {x : ℝ} (hx : x ∈ X) (turns : ℤ)
    {z : ℂ} {J : ComplexInterval} (hz : z ∈ J) :
    exp (I * (x : ℂ)) * z ∈ (rotation c P X turns).mul J :=
  mem_mul (mem_rotation hc hpi hx turns) hz

end PrimeFactorUnimodality.ComplexInterval
