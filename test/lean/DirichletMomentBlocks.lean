import PrimeFactorUnimodality.Helpers.Analytic.DirichletMomentBlocks
import PrimeFactorUnimodality.Helpers.Analytic.RadixTwiddleChecks

/-! # Shared-moment interfaces and small rational regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset LeanCert.Core
open PrimeFactorUnimodality.DirichletMomentBlock

variable {degree : ℕ}

example (r : MomentIntervalChunk) {c : SharedTaylorIntervals} (hc : c.Prepared)
    {P : IntervalRat} (hpi : Real.pi ∈ P) (base radius : ℚ) {degree : ℕ}
    (coefficients : Vector RationalPoint degree) (errors : Vector ℚ degree)
    (h : r.check c P base radius coefficients errors = true) :
    (ofChunk r coefficients errors).Valid base radius := by
  exact PrimeFactorUnimodality.DirichletMomentBlock.valid_of_check r hc hpi base radius coefficients errors h

example {degree : ℕ} {left right : DirichletMomentBlock degree}
    {base radius : ℝ} (hl : left.Valid base radius) (hr : right.Valid base radius)
    (hjoin : left.stop = right.first) (hgroup : left.group = right.group) :
    (left.append right).Valid base radius := by
  exact PrimeFactorUnimodality.DirichletMomentBlock.Valid.append hl hr hjoin hgroup

example {degree : ℕ} {r : DirichletMomentBlock degree} {base radius : ℝ}
    (hr : r.Valid base radius) (coefficients : Vector RationalPoint degree)
    (errors : Vector ℚ degree) (h : r.checkRounding coefficients errors = true) :
    (r.rounded coefficients errors).Valid base radius := by
  exact PrimeFactorUnimodality.DirichletMomentBlock.Valid.rounded hr coefficients errors h

def unitChunk : MomentIntervalChunk := ⟨1, 1, 0, #v[0]⟩
def emptyChunk : MomentIntervalChunk := ⟨2, 0, 0, #v[]⟩
def unitCoefficients : Vector RationalPoint 3 := #v[⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
def zeroErrors : Vector ℚ 3 := #v[0, 0, 0]

example : (ofChunk unitChunk unitCoefficients zeroErrors).checkRounding
    unitCoefficients zeroErrors = true := by decide +kernel
example : (ofChunk unitChunk unitCoefficients zeroErrors).checkRounding
    (Vector.replicate 3 ⟨0, 0⟩) zeroErrors = false := by decide +kernel
example : (ofChunk unitChunk unitCoefficients zeroErrors).checkRounding
    (Vector.replicate 3 ⟨0, 0⟩) (Vector.replicate 3 1) = true := by decide +kernel
example : (ofChunk unitChunk unitCoefficients zeroErrors).Valid 1000000000 10 := by
  simpa using valid_of_check unitChunk (SharedTaylorIntervals.prepare_prepared 0) pi_mem_twiddlePi
    1000000000 10 unitCoefficients zeroErrors (by decide +kernel)
example : ((ofChunk unitChunk unitCoefficients zeroErrors).append
    (ofChunk emptyChunk (Vector.replicate 3 ⟨0, 0⟩) zeroErrors)).Valid 0 0 := by
  apply Valid.append
  · simpa using valid_of_check unitChunk (SharedTaylorIntervals.prepare_prepared 0) pi_mem_twiddlePi
      0 0 unitCoefficients zeroErrors (by decide +kernel)
  · simpa using valid_of_check emptyChunk (SharedTaylorIntervals.prepare_prepared 0) pi_mem_twiddlePi
      0 0 (Vector.replicate 3 ⟨0, 0⟩) zeroErrors (by decide +kernel)
  · rfl
  · rfl

end

end PrimeFactorUnimodality.Tests
