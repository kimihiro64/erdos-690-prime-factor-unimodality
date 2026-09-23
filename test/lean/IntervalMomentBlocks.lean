import Mathlib.Tactic.FinCases
import PrimeFactorUnimodality.Helpers.Analytic.CheckedZetaMoments
import PrimeFactorUnimodality.Helpers.Analytic.IntervalMomentBlocks
import PrimeFactorUnimodality.Helpers.Analytic.RadixTwiddleChecks
import PrimeFactorUnimodality.Helpers.Analytic.RationalGridRadiusIntervals

/-! # Real-radius moments and exact rational-grid regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open PrimeFactorUnimodality.DirichletMomentBlock

example (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P B R : IntervalRat} (hpi : Real.pi ∈ P)
    {base radius : ℝ} (hb : base ∈ B) (hr : radius ∈ R) {degree : ℕ}
    (coefficients : Vector RationalPoint degree) (errors : Vector ℚ degree)
    (h : r.checkIntervals c P B R coefficients errors = true) :
    (ofChunk r coefficients errors).Valid base radius := by
  exact PrimeFactorUnimodality.DirichletMomentBlock.valid_of_interval_check r hc hpi hb hr coefficients errors h

def positivePi : IntervalRat.IntervalRatNonzero :=
  ⟨twiddlePi, by norm_num [IntervalRat.containsZero, twiddlePi]⟩
def reciprocalRadius : IntervalRat := rationalGridRadiusInterval positivePi 1

def radiusChunk : MomentIntervalChunk := ⟨1, 1, 0, #v[0]⟩
def radiusCoefficients : Vector RationalPoint 3 := #v[⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
def radiusErrors : Vector ℚ 3 := #v[0, 0, 0]

theorem reciprocalBlock_valid : (ofChunk radiusChunk radiusCoefficients radiusErrors).Valid
    1000000000 (rationalGridRadius 1) := by
  simpa using valid_of_interval_check radiusChunk (SharedTaylorIntervals.prepare_prepared 0)
    pi_mem_twiddlePi (IntervalRat.mem_singleton 1000000000)
    (mem_rationalGridRadiusInterval positivePi pi_mem_twiddlePi 1)
    radiusCoefficients radiusErrors (by decide +kernel)

def reciprocalBlock : DirichletMomentBlock 3 := ofChunk radiusChunk radiusCoefficients radiusErrors
def reciprocalBase : ZetaGroupedBlock :=
  ⟨1, 0, 3, 1000000000, rationalGridRadius 1, {0}, binAt [reciprocalBlock],
    fun _ _ => 0, fun _ _ => 0⟩
def reciprocalGrid : RationalGridRows :=
  ⟨[0], fun _ j => if j = 0 then ⟨1, 0⟩ else ⟨0, 0⟩, 0,
    ⟨fun n => Vector.replicate (2 ^ (n + 1)) ⟨1, 0⟩, fun _ => 0⟩,
    fun j => .leaf (if j = 0 then ⟨1, 0⟩ else ⟨0, 0⟩) 0⟩

example : (reciprocalGrid.attach reciprocalBase).Valid := by
  apply reciprocalGrid.valid_of_moment_blocks reciprocalBase [reciprocalBlock]
    (by decide) ?_ (by decide) ?_ (by decide) rfl ?_ ?_ 0 (by decide +kernel)
  · exact (checkChain_eq_true 1 2 [reciprocalBlock]).mp (by decide +kernel)
  · intro a ha
    have he : a = reciprocalBlock := List.mem_singleton.mp ha
    subst a
    exact reciprocalBlock_valid
  · intro a ha j
    have he : a = reciprocalBlock := List.mem_singleton.mp ha
    subst a
    change Fin 3 at j
    fin_cases j <;> rfl
  · intro a ha j
    have he : a = reciprocalBlock := List.mem_singleton.mp ha
    subst a
    change Fin 3 at j
    fin_cases j <;> change ((0 : ℚ) : ℝ) ≤ 0 <;> norm_num

end

end PrimeFactorUnimodality.Tests
