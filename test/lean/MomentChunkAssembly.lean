import PrimeFactorUnimodality.Helpers.Analytic.MomentChunkAssembly

/-! # Real-radius moments and exact rational-grid regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open PrimeFactorUnimodality.MomentIntervalChunk

example (r : MomentIntervalChunk) (degree : ℕ)
    (atom : ℕ → DirichletAtomInterval) (weight : ℕ → ℂ) (frequency : ℕ → ℝ)
    (ha : ∀ n ∈ Ico r.first (r.first + r.count),
      weight n ∈ (atom n).weight ∧ frequency n ∈ (atom n).residual) (j : Fin degree) :
    expSumMoment (Ico r.first (r.first + r.count)) weight frequency j.val ∈
      (r.evaluateAtoms degree atom).columns[j.val] := by
  exact PrimeFactorUnimodality.MomentIntervalChunk.evaluateAtoms_mem r degree atom weight frequency ha j

example (r : MomentIntervalChunk) (degree : ℕ)
    (atom : ℕ → DirichletAtomInterval) (frequency : ℕ → ℝ)
    (ha : ∀ n ∈ Ico r.first (r.first + r.count), frequency n ∈ (atom n).residual)
    (h : (r.evaluateAtoms degree atom).residuals = true)
    {n : ℕ} (hn : n ∈ Ico r.first (r.first + r.count)) : |frequency n| ≤ (1 / 2 : ℝ) := by
  exact PrimeFactorUnimodality.MomentIntervalChunk.evaluateAtoms_residuals r degree atom frequency ha h hn

def constantAtom (_ : ℕ) : DirichletAtomInterval :=
  ⟨ComplexInterval.point ⟨1, 0⟩, IntervalRat.singleton 0⟩
example : ((MomentIntervalChunk.mk 1 2 0 #v[0, 0]).evaluateAtoms 2 constantAtom).columns =
    #v[ComplexInterval.point ⟨2, 0⟩, ComplexInterval.point ⟨0, 0⟩] := by decide +kernel
example : ((MomentIntervalChunk.mk 1 0 0 #v[]).evaluateAtoms 1 constantAtom).columns =
    #v[ComplexInterval.point ⟨0, 0⟩] := by decide +kernel

end

end PrimeFactorUnimodality.Tests
