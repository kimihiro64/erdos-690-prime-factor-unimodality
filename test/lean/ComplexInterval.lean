import PrimeFactorUnimodality.Helpers.Analytic.ComplexInterval

/-! # Shared-moment interfaces and small rational regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset LeanCert.Core
open PrimeFactorUnimodality.ComplexInterval

variable {degree : ℕ}

example (q : RationalPoint) : q.toComplex ∈ point q := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_point q

example {x : ℝ} {J : IntervalRat} (hx : x ∈ J) : (x : ℂ) ∈ real J := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_real hx

example {x : ℝ} {J : IntervalRat} (hx : x ∈ J) : I * (x : ℂ) ∈ imag J := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_imag hx

example {z w : ℂ} {J K : ComplexInterval} (hz : z ∈ J) (hw : w ∈ K) :
    z + w ∈ add J K := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_add hz hw

example {z w : ℂ} {J K : ComplexInterval} (hz : z ∈ J) (hw : w ∈ K) :
    z * w ∈ mul J K := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_mul hz hw

example (q : ℚ) {z : ℂ} {J : ComplexInterval} (hz : z ∈ J) :
    (q : ℂ) * z ∈ scale q J := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_scale q hz

example {J K : ComplexInterval} (h : subset J K = true)
    {z : ℂ} (hz : z ∈ J) : z ∈ K := by
  exact PrimeFactorUnimodality.ComplexInterval.mem_of_subset h hz

example {J : ComplexInterval} {q : RationalPoint} {e : ℚ}
    (h : close J q e = true) {z : ℂ} (hz : z ∈ J) :
    ‖z - q.toComplex‖ ≤ (e : ℝ) := by
  exact PrimeFactorUnimodality.ComplexInterval.norm_sub_le_of_close h hz

example : (point ⟨3, 4⟩).close ⟨0, 0⟩ 5 = true := by decide +kernel
example : (point ⟨3, 4⟩).close ⟨0, 0⟩ (499 / 100) = false := by decide +kernel
example : (point ⟨0, 0⟩).close ⟨0, 0⟩ (-1) = false := by decide +kernel
example : (point ⟨1, 0⟩).subset (point ⟨0, 0⟩) = false := by decide +kernel

end

end PrimeFactorUnimodality.Tests
