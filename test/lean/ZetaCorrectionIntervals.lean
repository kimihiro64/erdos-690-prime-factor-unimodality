import PrimeFactorUnimodality.Helpers.Analytic.RadixTwiddleChecks
import PrimeFactorUnimodality.Helpers.Analytic.ZetaCorrectionIntervals

/-! # Short Euler-correction interfaces and exact regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Polynomial
open LeanCert.Core
open PrimeFactorUnimodality.ZetaCorrectionIntervals

example {t : ℝ} {T : IntervalRat} (ht : t ∈ T) :
    (1 / 2 : ℂ) + t * I ∈ critical T := by
  exact PrimeFactorUnimodality.ZetaCorrectionIntervals.mem_critical ht

example {N m : ℕ} {T : IntervalRat} {t : ℝ} (ht : t ∈ T)
    {coefficients : List ℚ} (hb : coefficients = eulerBernoulliCoefficients 1 m)
    {J : ComplexInterval} (hJ : factor? N T coefficients = some J) :
    let s := (1 / 2 : ℂ) + t * I
    (N : ℂ) / (s - 1) - 1 / 2 +
      ((List.range' 1 m).map (fun j =>
        (bernoulliNormalizedReal (j + 1) 0 : ℂ) *
          (zetaRisingFactor s j / (N : ℂ) ^ j))).sum ∈ J := by
  exact PrimeFactorUnimodality.ZetaCorrectionIntervals.mem_factor ht hb hJ

example {d : DirichletEndpointIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {P T : IntervalRat}
    (hpi : Real.pi ∈ P) {t : ℝ} (ht : t ∈ T) (turns : ℤ)
    {m : ℕ} {coefficients : List ℚ} (hb : coefficients = eulerBernoulliCoefficients 1 m)
    {J : ComplexInterval} (hJ : evaluate? d c P T turns coefficients = some J) :
    zetaEulerCorrection d.cutoff ((1 / 2 : ℂ) + t * I) m ∈ J := by
  exact PrimeFactorUnimodality.ZetaCorrectionIntervals.mem_evaluate hd hc hpi ht turns hb hJ

example {d : DirichletEndpointIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {P T : IntervalRat}
    (hpi : Real.pi ∈ P) {t : ℝ} (ht : t ∈ T) (turns : ℤ)
    {m : ℕ} {coefficients : List ℚ} (hb : coefficients = eulerBernoulliCoefficients 1 m)
    {q : RationalPoint} {e : ℚ} (h : check d c P T turns coefficients q e = true) :
    ‖zetaEulerCorrection d.cutoff ((1 / 2 : ℂ) + t * I) m - q.toComplex‖ ≤ (e : ℝ) := by
  exact PrimeFactorUnimodality.ZetaCorrectionIntervals.norm_sub_le_of_check hd hc hpi ht turns hb h

def scalarConfig : SharedTaylorIntervals := SharedTaylorIntervals.prepare 0
def unitEndpoint : DirichletEndpointIntervals := DirichletEndpointIntervals.prepare scalarConfig 1
def zeroHeight : IntervalRat := IntervalRat.singleton 0

example : check unitEndpoint scalarConfig twiddlePi zeroHeight 0 [] ⟨-5 / 2, 0⟩ 0 = true :=
  by decide +kernel
example : check unitEndpoint scalarConfig twiddlePi zeroHeight 0 [1 / 12]
    ⟨-59 / 24, 0⟩ 0 = true := by decide +kernel
example : check unitEndpoint scalarConfig twiddlePi zeroHeight 0 [1 / 12, 0, -1 / 720]
    ⟨-315 / 128, 0⟩ 0 = true := by decide +kernel
example : check unitEndpoint scalarConfig twiddlePi zeroHeight 0 [] ⟨0, 0⟩ 0 = false :=
  by decide +kernel
example : check unitEndpoint scalarConfig twiddlePi zeroHeight 0 [] ⟨-5 / 2, 0⟩ (-1) = false :=
  by decide +kernel
example : factor? 1 ⟨-1, 1, by norm_num⟩ [] = none := by decide +kernel
example : ‖zetaEulerCorrection 1 (1 / 2 : ℂ) 3 -
    (RationalPoint.mk (-315 / 128) 0).toComplex‖ ≤ 0 := by
  simpa [unitEndpoint, DirichletEndpointIntervals.prepare] using norm_sub_le_of_check
    (DirichletEndpointIntervals.prepare_valid (SharedTaylorIntervals.prepare_prepared 0) 1 (by decide))
    (SharedTaylorIntervals.prepare_prepared 0) pi_mem_twiddlePi
    (IntervalRat.mem_singleton 0) 0
    (m := 3) (coefficients := [1 / 12, 0, -1 / 720]) (by decide +kernel)
    (q := ⟨-315 / 128, 0⟩) (e := 0) (by decide +kernel)

end

end PrimeFactorUnimodality.Tests
