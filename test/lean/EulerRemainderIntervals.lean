import PrimeFactorUnimodality.Helpers.Analytic.EulerRemainderIntervals

/-! # Full grid-error interfaces and small rational boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open Polynomial
open PrimeFactorUnimodality

example (N k : ℕ) {s : ℂ} {S : ComplexInterval} (hs : s ∈ S) :
    zetaRisingFactor s k / (N : ℂ) ^ k ∈ eulerRisingInterval N S k := by
  exact PrimeFactorUnimodality.mem_eulerRisingInterval N k hs

example (N m : ℕ) (hN : 0 < N) {s : ℂ} (hs : s.re = 1 / 2) :
    zetaEulerError N s m = (bernoulliCoeffBound (m + 1) : ℝ) *
      ‖zetaRisingFactor s (m + 1) / (N : ℂ) ^ (m + 1)‖ * N *
        Real.exp (-Real.log N / 2) / (1 / 2 + (m : ℝ)) := by
  exact PrimeFactorUnimodality.zetaEulerError_eq_scaled N m hN hs

example {d : DirichletEndpointIntervals} (hd : d.Valid)
    {s : ℂ} {S : ComplexInterval} (hs : s ∈ S) (hsre : s.re = 1 / 2)
    (m : ℕ) {C M E : ℚ} (hC : C = bernoulliCoeffBudget (m + 1))
    (h : checkEulerRemainder d S m C M E = true) :
    zetaEulerError d.cutoff s m ≤ (E : ℝ) := by
  exact PrimeFactorUnimodality.zetaEulerError_le_of_check hd hs hsre m hC h

def unitEndpoint : DirichletEndpointIntervals :=
  ⟨1, IntervalRat.singleton 0, IntervalRat.singleton 1⟩
example : eulerRisingInterval 2 (ComplexInterval.point ⟨1, 0⟩) 2 =
    ComplexInterval.point ⟨1 / 2, 0⟩ := by decide +kernel
example : checkEulerRemainder unitEndpoint (ComplexInterval.point ⟨1 / 2, 0⟩)
    0 (3 / 2) (1 / 2) (3 / 2) = true := by decide +kernel
example : checkEulerRemainder unitEndpoint (ComplexInterval.point ⟨1 / 2, 0⟩)
    0 (3 / 2) (2 / 5) (3 / 2) = false := by decide +kernel
example : checkEulerRemainder unitEndpoint (ComplexInterval.point ⟨1 / 2, 0⟩)
    0 (3 / 2) (1 / 2) 1 = false := by decide +kernel
example : zetaEulerError 1 (1 / 2 : ℂ) 0 ≤ (3 / 2 : ℝ) := by
  have hd : unitEndpoint.Valid := by
    refine ⟨by decide, ?_, ?_⟩ <;>
      norm_num [unitEndpoint, IntervalRat.mem_def, IntervalRat.singleton]
  have h := zetaEulerError_le_of_check hd
    (ComplexInterval.mem_constant (1 / 2)) (by norm_num) 0
    (show (3 / 2 : ℚ) = bernoulliCoeffBudget 1 from by decide +kernel)
    (show checkEulerRemainder unitEndpoint (ComplexInterval.point ⟨1 / 2, 0⟩)
      0 (3 / 2) (1 / 2) (3 / 2) = true from by decide +kernel)
  simpa [unitEndpoint] using h

end

end PrimeFactorUnimodality.Tests
