import PrimeFactorUnimodality.Helpers.Analytic.RadixTwiddleChecks
import PrimeFactorUnimodality.Helpers.Analytic.XiSimplePhaseIntervals

/-! # Checked elementary xi-phase interfaces and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open PrimeFactorUnimodality.XiSimplePhaseIntervals

example {c : SharedTaylorIntervals} (hc : c.Prepared) {P : IntervalRat}
    (hP : 0 < P.lo) (hpi : Real.pi ∈ P) : (prepare c P).Valid := by
  exact PrimeFactorUnimodality.XiSimplePhaseIntervals.prepare_valid hc hP hpi

example {d : XiSimplePhaseIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {T : IntervalRat}
    (hT : 0 < T.lo) {t : ℝ} (ht : t ∈ T) : xiSimplePhase t ∈ d.evaluate c T := by
  exact PrimeFactorUnimodality.XiSimplePhaseIntervals.mem_evaluate hd hc hT ht

example {d : XiSimplePhaseIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {T : IntervalRat} {t : ℝ} (ht : t ∈ T)
    {phase error : ℚ} (h : d.check c T phase error = true) :
    |turingStirlingPhase t - (phase : ℝ)| ≤ (error : ℝ) := by
  exact PrimeFactorUnimodality.XiSimplePhaseIntervals.abs_stirling_sub_le_of_check hd hc ht h

example {d : XiSimplePhaseIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {T : IntervalRat} {t : ℝ} (ht : t ∈ T)
    {phase error : ℚ} (h : d.check c T phase error = true) :
    |turingCountingPhase t - (phase : ℝ)| ≤ 1 / 10 + (error : ℝ) := by
  exact PrimeFactorUnimodality.XiSimplePhaseIntervals.abs_counting_sub_le_of_check hd hc ht h

def phaseConfig : SharedTaylorIntervals := SharedTaylorIntervals.prepare 0
def phaseConstants : XiSimplePhaseIntervals := XiSimplePhaseIntervals.prepare phaseConfig twiddlePi
def sampleHeight : IntervalRat := IntervalRat.singleton 2

theorem phaseConstants_valid : phaseConstants.Valid :=
  XiSimplePhaseIntervals.prepare_valid (SharedTaylorIntervals.prepare_prepared 0)
    (by decide +kernel) pi_mem_twiddlePi

example : phaseConstants.check phaseConfig sampleHeight 0 100 = true := by decide +kernel
example : phaseConstants.check phaseConfig sampleHeight 0 0 = false := by decide +kernel
example : phaseConstants.check phaseConfig (IntervalRat.singleton 0) 0 100 = false :=
  by decide +kernel
example : phaseConstants.check phaseConfig (IntervalRat.singleton (-2)) 0 100 = false :=
  by decide +kernel
example : phaseConstants.check phaseConfig ⟨2, 3, by norm_num⟩ 0 100 = true := by decide +kernel
example : |turingStirlingPhase 2| ≤ 100 := by
  simpa using abs_stirling_sub_le_of_check phaseConstants_valid
    (SharedTaylorIntervals.prepare_prepared 0) (IntervalRat.mem_singleton 2)
    (phase := 0) (error := 100) (by decide +kernel)
example : |turingCountingPhase 2| ≤ (1001 / 10 : ℝ) := by
  have h := abs_counting_sub_le_of_check phaseConstants_valid
    (SharedTaylorIntervals.prepare_prepared 0) (IntervalRat.mem_singleton 2)
    (phase := 0) (error := 100) (by decide +kernel)
  norm_num at h ⊢
  exact h

end

end PrimeFactorUnimodality.Tests
