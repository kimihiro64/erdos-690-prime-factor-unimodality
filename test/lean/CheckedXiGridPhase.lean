import PrimeFactorUnimodality.Helpers.Analytic.CheckedXiGridPhase
import PrimeFactorUnimodality.Helpers.Analytic.RadixTwiddleChecks

/-! # Checked elementary xi-phase interfaces and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open PrimeFactorUnimodality.RationalGridPoint

example (p : RationalGridPoint) {g : ZetaGridBlock}
    (hg : g.Valid) {d : DirichletEndpointIntervals} (hd : d.Valid)
    (hN : d.cutoff = g.shared.cutoff) {c : SharedTaylorIntervals} (hc : c.Prepared)
    {P B R : IntervalRat} (hpi : Real.pi ∈ P) (hbase : g.shared.base ∈ B)
    (hradius : g.shared.radius ∈ R) {coefficients : List ℚ}
    (hb : coefficients = eulerBernoulliCoefficients 1 g.shared.order)
    (h : p.check g.levels d c P B R coefficients = true)
    {phaseData : XiSimplePhaseIntervals} (hp : phaseData.Valid) {phase error : ℚ}
    (hphase : phaseData.check c (p.heightInterval g.levels P B R) phase error = true) :
    |xiNormalizedValue (p.toGridPoint.height g) - p.toGridPoint.xiApprox g phase| ≤
      p.toGridPoint.xiError g error := by
  exact PrimeFactorUnimodality.RationalGridPoint.abs_xi_sub_approx_le_of_checks p hg hd hN hc hpi hbase hradius hb h hp hphase

def phaseConfig : SharedTaylorIntervals := SharedTaylorIntervals.prepare 0
def phaseConstants : XiSimplePhaseIntervals := XiSimplePhaseIntervals.prepare phaseConfig twiddlePi
def sampleHeight : IntervalRat := IntervalRat.singleton 2

theorem phaseConstants_valid : phaseConstants.Valid :=
  XiSimplePhaseIntervals.prepare_valid (SharedTaylorIntervals.prepare_prepared 0)
    (by decide +kernel) pi_mem_twiddlePi

def phasePoint : RationalGridPoint := ⟨0, 0, ⟨-21 / 34, -8 / 17⟩, 0⟩
def phaseBase : ZetaGroupedBlock :=
  ⟨1, 0, 0, 2, 0, {0}, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩
def phaseGrid : ZetaGridBlock := ⟨phaseBase, 0, fun _ => .leaf 0 0⟩

theorem phaseGrid_valid : phaseGrid.Valid := by
  refine ⟨⟨by decide, ?_, ?_, ?_⟩, ?_⟩
  · intro n hn
    simp [phaseGrid, phaseBase]
  · intro n hn
    norm_num [phaseGrid, phaseBase, dirichletFrequency]
  · intro b hb j hj
    simp [phaseGrid, phaseBase] at hj
  · intro j hj
    simp [phaseGrid, phaseBase] at hj

example : |xiNormalizedValue (phasePoint.toGridPoint.height phaseGrid) -
    phasePoint.toGridPoint.xiApprox phaseGrid 0| ≤ phasePoint.toGridPoint.xiError phaseGrid 100 := by
  simpa using phasePoint.abs_xi_sub_approx_le_of_checks phaseGrid_valid
    (DirichletEndpointIntervals.prepare_valid (SharedTaylorIntervals.prepare_prepared 0) 1 (by decide))
    rfl (SharedTaylorIntervals.prepare_prepared 0) pi_mem_twiddlePi
    (by simpa [phaseGrid, phaseBase] using IntervalRat.mem_singleton 2)
    (by simpa [phaseGrid, phaseBase] using IntervalRat.mem_singleton 0)
    (coefficients := []) rfl (by decide +kernel) phaseConstants_valid
    (phase := 0) (error := 100) (by decide +kernel)

end

end PrimeFactorUnimodality.Tests
