import PrimeFactorUnimodality.Helpers.Analytic.EulerBernoulliIntervals

/-! # Short Euler-correction interfaces and exact regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Polynomial
open LeanCert.Core
open PrimeFactorUnimodality

example (N k : ℕ) {s : ℂ} {S W : ComplexInterval}
    (hs : s ∈ S) (hw : zetaRisingFactor s k / (N : ℂ) ^ k ∈ W) :
    zetaRisingFactor s (k + 1) / (N : ℂ) ^ (k + 1) ∈ eulerRisingStep N S k W := by
  exact PrimeFactorUnimodality.mem_eulerRisingStep N k hs hw

example (N : ℕ) {s : ℂ} {S : ComplexInterval} (hs : s ∈ S)
    (start count : ℕ) {W : ComplexInterval}
    (hw : zetaRisingFactor s start / (N : ℂ) ^ start ∈ W) :
    ((List.range' start count).map (fun j =>
      (bernoulliNormalizedReal (j + 1) 0 : ℂ) *
        (zetaRisingFactor s j / (N : ℂ) ^ j))).sum ∈
      eulerBernoulliInterval N S start W (eulerBernoulliCoefficients start count) := by
  exact PrimeFactorUnimodality.mem_eulerBernoulliInterval N hs start count hw

example : eulerBernoulliCoefficients 1 0 = [] := by decide +kernel
example : eulerBernoulliCoefficients 1 3 = [1 / 12, 0, -1 / 720] := by decide +kernel
example : eulerRisingStep 1 (ComplexInterval.point ⟨1 / 2, 0⟩) 1
    (ComplexInterval.point ⟨1 / 2, 0⟩) = ComplexInterval.point ⟨3 / 4, 0⟩ := by decide +kernel
example : eulerBernoulliInterval 1 (ComplexInterval.point ⟨1 / 2, 0⟩) 1
    (ComplexInterval.point ⟨1 / 2, 0⟩) [1 / 12, 0, -1 / 720] =
      ComplexInterval.point ⟨5 / 128, 0⟩ := by decide +kernel

end

end PrimeFactorUnimodality.Tests
