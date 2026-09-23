import PrimeFactorUnimodality.Helpers.Analytic.ComplexIntervalInverse

/-! # Short Euler-correction interfaces and exact regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Polynomial
open LeanCert.Core
open PrimeFactorUnimodality.ComplexInterval

example {z : ℂ} {J : ComplexInterval} (hz : z ∈ J) :
    Complex.normSq z ∈ normSquared J := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_normSquared hz

example {J K : ComplexInterval} (h : inverse? J = some K)
    {z : ℂ} (hz : z ∈ J) : z⁻¹ ∈ K := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_inverse h hz

example : (point ⟨3, 4⟩).inverse? = some (point ⟨3 / 25, -4 / 25⟩) := by decide +kernel
example : (point ⟨0, 0⟩).inverse? = none := by decide +kernel
example : (point ⟨-1, 0⟩).inverse? = some (point ⟨-1, 0⟩) := by decide +kernel
example : (point ⟨0, 1⟩).inverse? = some (point ⟨0, -1⟩) := by decide +kernel
example : (ComplexInterval.mk ⟨-1, 1, by norm_num⟩ ⟨-1, 1, by norm_num⟩).inverse? = none :=
  by decide +kernel

end

end PrimeFactorUnimodality.Tests
