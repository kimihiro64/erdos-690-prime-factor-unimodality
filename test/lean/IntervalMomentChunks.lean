import PrimeFactorUnimodality.Helpers.Analytic.IntervalMomentChunks
import PrimeFactorUnimodality.Helpers.Analytic.RadixTwiddleChecks
import PrimeFactorUnimodality.Helpers.Analytic.RationalGridRadiusIntervals

/-! # Real-radius moments and exact rational-grid regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open PrimeFactorUnimodality.MomentIntervalChunk

example (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P B R : IntervalRat} (hpi : Real.pi ∈ P)
    {base radius : ℝ} (hb : base ∈ B) (hr : radius ∈ R) (n : ℕ) (hn : 0 < n) :
    1 / (n : ℂ) ^ ((1 / 2 : ℂ) + base * I) ∈ (r.intervalAtom c P B R n).weight ∧
      -radius * Real.log n - r.group ∈ (r.intervalAtom c P B R n).residual := by
  exact PrimeFactorUnimodality.MomentIntervalChunk.intervalAtom_sound r hc hpi hb hr n hn

example (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P B R : IntervalRat} (hpi : Real.pi ∈ P)
    {base radius : ℝ} (hb : base ∈ B) (hr : radius ∈ R) (degree : ℕ)
    (hfirst : 0 < r.first) (j : Fin degree) :
    expSumMoment (Ico r.first (r.first + r.count))
      (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + base * I))
      (fun n => -radius * Real.log n - r.group) j.val ∈
        (r.evaluateIntervals c P B R degree).columns[j.val] := by
  exact PrimeFactorUnimodality.MomentIntervalChunk.evaluateIntervals_mem r hc hpi hb hr degree hfirst j

example (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P B R : IntervalRat} (hpi : Real.pi ∈ P)
    {base radius : ℝ} (hb : base ∈ B) (hr : radius ∈ R) (degree : ℕ)
    (hfirst : 0 < r.first) (h : (r.evaluateIntervals c P B R degree).residuals = true)
    {n : ℕ} (hn : n ∈ Ico r.first (r.first + r.count)) :
    |-radius * Real.log n - r.group| ≤ (1 / 2 : ℝ) := by
  exact PrimeFactorUnimodality.MomentIntervalChunk.evaluateIntervals_residuals r hc hpi hb hr degree hfirst h hn

example (r : MomentIntervalChunk) {c : SharedTaylorIntervals}
    (hc : c.Prepared) {P B R : IntervalRat} (hpi : Real.pi ∈ P)
    {base radius : ℝ} (hb : base ∈ B) (hr : radius ∈ R) {degree : ℕ}
    (coefficients : Vector RationalPoint degree) (errors : Vector ℚ degree)
    (h : r.checkIntervals c P B R coefficients errors = true) (j : Fin degree) :
    ‖expSumMoment (Ico r.first (r.first + r.count))
        (fun n => 1 / (n : ℂ) ^ ((1 / 2 : ℂ) + base * I))
        (fun n => -radius * Real.log n - r.group) j.val -
          coefficients[j.val].toComplex‖ ≤ (errors[j.val] : ℝ) := by
  exact PrimeFactorUnimodality.MomentIntervalChunk.checkIntervals_moments r hc hpi hb hr coefficients errors h j

def positivePi : IntervalRat.IntervalRatNonzero :=
  ⟨twiddlePi, by norm_num [IntervalRat.containsZero, twiddlePi]⟩
def reciprocalRadius : IntervalRat := rationalGridRadiusInterval positivePi 1

def radiusChunk : MomentIntervalChunk := ⟨1, 1, 0, #v[0]⟩
def radiusCoefficients : Vector RationalPoint 3 := #v[⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]
def radiusErrors : Vector ℚ 3 := #v[0, 0, 0]

example : radiusChunk.checkIntervals (SharedTaylorIntervals.prepare 0) twiddlePi
    (IntervalRat.singleton 1000000000) reciprocalRadius radiusCoefficients radiusErrors = true :=
  by decide +kernel
example : ({radiusChunk with first := 0}).checkIntervals (SharedTaylorIntervals.prepare 0) twiddlePi
    (IntervalRat.singleton 1000000000) reciprocalRadius radiusCoefficients radiusErrors = false :=
  by decide +kernel
example : ({radiusChunk with group := 1}).checkIntervals (SharedTaylorIntervals.prepare 0) twiddlePi
    (IntervalRat.singleton 1000000000) reciprocalRadius radiusCoefficients radiusErrors = false :=
  by decide +kernel
example : radiusChunk.checkIntervals (SharedTaylorIntervals.prepare 0) twiddlePi
    (IntervalRat.singleton 1000000000) reciprocalRadius (Vector.replicate 3 ⟨0, 0⟩) radiusErrors =
      false := by decide +kernel

end

end PrimeFactorUnimodality.Tests
