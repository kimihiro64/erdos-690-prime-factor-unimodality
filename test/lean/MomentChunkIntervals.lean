import PrimeFactorUnimodality.Helpers.Analytic.MomentChunkIntervals
import PrimeFactorUnimodality.Helpers.Analytic.RadixTwiddleChecks

/-! # Shared-moment interfaces and small rational regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset LeanCert.Core
open PrimeFactorUnimodality

variable {degree : ℕ}

example {R : IntervalRat}
    (h : residualWithinHalf R = true) {x : ℝ} (hx : x ∈ R) : |x| ≤ (1 / 2 : ℝ) := by
  exact PrimeFactorUnimodality.abs_le_half_of_residualWithinHalf h hx

example (r : MomentIntervalChunk) {c : SharedTaylorIntervals} (hc : c.Prepared)
    {P : IntervalRat} (hpi : Real.pi ∈ P) (base radius : ℚ) (degree : ℕ)
    (hfirst : 0 < r.first) (j : Fin degree) :
    expSumMoment (Ico r.first (r.first + r.count))
      (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + (base : ℂ) * I))
      (fun n => -(radius : ℝ) * Real.log n - r.group) j.val ∈
        (r.evaluate c P base radius degree).columns[j.val] := by
  exact PrimeFactorUnimodality.MomentIntervalChunk.evaluate_mem r hc hpi base radius degree hfirst j

example (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P : IntervalRat} (hpi : Real.pi ∈ P)
    (base radius : ℚ) (degree : ℕ) (hfirst : 0 < r.first)
    (h : (r.evaluate c P base radius degree).residuals = true)
    {n : ℕ} (hn : n ∈ Ico r.first (r.first + r.count)) :
    |-(radius : ℝ) * Real.log n - r.group| ≤ (1 / 2 : ℝ) := by
  exact PrimeFactorUnimodality.MomentIntervalChunk.evaluate_residuals r hc hpi base radius degree hfirst h hn

example (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P : IntervalRat} (hpi : Real.pi ∈ P)
    (base radius : ℚ) {degree : ℕ} (coefficients : Vector RationalPoint degree)
    (errors : Vector ℚ degree) (h : r.check c P base radius coefficients errors = true)
    (j : Fin degree) :
    ‖expSumMoment (Ico r.first (r.first + r.count))
        (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + (base : ℂ) * I))
        (fun n => -(radius : ℝ) * Real.log n - r.group) j.val -
          coefficients[j.val].toComplex‖ ≤ (errors[j.val] : ℝ) := by
  exact PrimeFactorUnimodality.MomentIntervalChunk.check_moments r hc hpi base radius coefficients errors h j

def unitChunk : MomentIntervalChunk := ⟨1, 1, 0, #v[0]⟩
def emptyChunk : MomentIntervalChunk := ⟨2, 0, 0, #v[]⟩
def unitCoefficients : Vector RationalPoint 3 := #v[⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
def zeroErrors : Vector ℚ 3 := #v[0, 0, 0]

example : unitChunk.check (SharedTaylorIntervals.prepare 0) twiddlePi 1000000000 10
    unitCoefficients zeroErrors = true := by decide +kernel
example : emptyChunk.check (SharedTaylorIntervals.prepare 0) twiddlePi 0 0
    (Vector.replicate 3 ⟨0, 0⟩) zeroErrors = true := by decide +kernel
example : ({unitChunk with group := 1}).check (SharedTaylorIntervals.prepare 0) twiddlePi 0 0
    unitCoefficients zeroErrors = false := by decide +kernel
example : ({unitChunk with first := 0}).check (SharedTaylorIntervals.prepare 0) twiddlePi 0 0
    unitCoefficients zeroErrors = false := by decide +kernel
example : unitChunk.check (SharedTaylorIntervals.prepare 0) twiddlePi 0 0
    (Vector.replicate 3 ⟨0, 0⟩) zeroErrors = false := by decide +kernel

end

end PrimeFactorUnimodality.Tests
