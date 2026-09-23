import PrimeFactorUnimodality.Helpers.Analytic.DirichletEndpointIntervals
import PrimeFactorUnimodality.Helpers.Analytic.RadixTwiddleChecks

/-! # Short Euler-correction interfaces and exact regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Polynomial
open LeanCert.Core
open PrimeFactorUnimodality.DirichletEndpointIntervals

example {c : SharedTaylorIntervals} (hc : c.Prepared)
    (N : ℕ) (hN : 0 < N) : (prepare c N).Valid := by
  exact PrimeFactorUnimodality.DirichletEndpointIntervals.prepare_valid hc N hN

example {d : DirichletEndpointIntervals} (hd : d.Valid)
    {P T : IntervalRat} (hpi : Real.pi ∈ P) {t : ℝ} (ht : t ∈ T) (turns : ℤ) :
    -t * Real.log d.cutoff - (turns : ℝ) * (2 * Real.pi) ∈ d.phase P T turns := by
  exact PrimeFactorUnimodality.DirichletEndpointIntervals.mem_phase hd hpi ht turns

example {d : DirichletEndpointIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {P T : IntervalRat}
    (hpi : Real.pi ∈ P) {t : ℝ} (ht : t ∈ T) (turns : ℤ) :
    1 / (d.cutoff : ℂ) ^ ((1 / 2 : ℂ) + t * I) ∈ d.weight c P T turns := by
  exact PrimeFactorUnimodality.DirichletEndpointIntervals.mem_weight hd hc hpi ht turns

def scalarConfig : SharedTaylorIntervals := SharedTaylorIntervals.prepare 0
def unitEndpoint : DirichletEndpointIntervals := DirichletEndpointIntervals.prepare scalarConfig 1
def zeroHeight : IntervalRat := IntervalRat.singleton 0

example : unitEndpoint.Valid := prepare_valid (SharedTaylorIntervals.prepare_prepared 0) 1 (by decide)
example : unitEndpoint.weight scalarConfig twiddlePi ⟨-1000000000, 1000000000, by norm_num⟩ 0 =
    ComplexInterval.point ⟨1, 0⟩ := by decide +kernel

end

end PrimeFactorUnimodality.Tests
