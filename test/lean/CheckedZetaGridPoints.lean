import PrimeFactorUnimodality.Helpers.Analytic.CheckedZetaGridPoints
import PrimeFactorUnimodality.Helpers.Analytic.RadixTwiddleChecks

/-! # Short Euler-correction interfaces and exact regression cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset Polynomial
open LeanCert.Core
open PrimeFactorUnimodality

example {P : IntervalRat} (hpi : Real.pi ∈ P)
    (levels : ℕ) (index : ℤ) :
    2 * Real.pi * index / (2 : ℝ) ^ levels ∈ zetaGridCoordinateInterval P levels index := by
  exact PrimeFactorUnimodality.mem_zetaGridCoordinateInterval hpi levels index

example {J : IntervalRat} (h : intervalWithinUnit J = true)
    {x : ℝ} (hx : x ∈ J) : |x| ≤ 1 := by
  exact PrimeFactorUnimodality.abs_le_one_of_intervalWithinUnit h hx

example (p : RationalGridPoint) {g : ZetaGridBlock}
    {d : DirichletEndpointIntervals} (hd : d.Valid) (hN : d.cutoff = g.shared.cutoff)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {P B R : IntervalRat}
    (hpi : Real.pi ∈ P) (hbase : g.shared.base ∈ B) (hradius : g.shared.radius ∈ R)
    {coefficients : List ℚ} (hb : coefficients = eulerBernoulliCoefficients 1 g.shared.order)
    (h : p.check g.levels d c P B R coefficients = true) : p.toGridPoint.Valid g := by
  exact PrimeFactorUnimodality.RationalGridPoint.valid_of_check p hd hN hc hpi hbase hradius hb h

example (p : RationalGridPoint) {g : ZetaGridBlock} (hg : g.Valid)
    {d : DirichletEndpointIntervals} (hd : d.Valid) (hN : d.cutoff = g.shared.cutoff)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {P B R : IntervalRat}
    (hpi : Real.pi ∈ P) (hbase : g.shared.base ∈ B) (hradius : g.shared.radius ∈ R)
    {coefficients : List ℚ} (hb : coefficients = eulerBernoulliCoefficients 1 g.shared.order)
    (h : p.check g.levels d c P B R coefficients = true) :
    ‖riemannZeta ((1 / 2 : ℂ) + p.toGridPoint.height g * I) - p.toGridPoint.value g‖ ≤
      p.toGridPoint.error g := by
  exact PrimeFactorUnimodality.RationalGridPoint.norm_zeta_sub_value_le p hg hd hN hc hpi hbase hradius hb h

def scalarConfig : SharedTaylorIntervals := SharedTaylorIntervals.prepare 0
def unitEndpoint : DirichletEndpointIntervals := DirichletEndpointIntervals.prepare scalarConfig 1
def zeroHeight : IntervalRat := IntervalRat.singleton 0

def unitPoint : RationalGridPoint := ⟨0, 0, ⟨-5 / 2, 0⟩, 0⟩
def emptyMomentBase : ZetaGroupedBlock :=
  ⟨1, 0, 0, 0, 0, {0}, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩
def emptyMomentGrid : ZetaGridBlock := ⟨emptyMomentBase, 0, fun _ => .leaf 0 0⟩

theorem emptyMomentGrid_valid : emptyMomentGrid.Valid := by
  refine ⟨⟨by decide, ?_, ?_, ?_⟩, ?_⟩
  · intro n hn
    simp [emptyMomentGrid, emptyMomentBase]
  · intro n hn
    norm_num [emptyMomentGrid, emptyMomentBase, dirichletFrequency]
  · intro b hb j hj
    simp [emptyMomentGrid, emptyMomentBase] at hj
  · intro j hj
    simp [emptyMomentGrid, emptyMomentBase] at hj

example : unitPoint.check 0 unitEndpoint scalarConfig twiddlePi zeroHeight zeroHeight [] = true :=
  by decide +kernel
example : ({unitPoint with index := 1}).check 0 unitEndpoint scalarConfig twiddlePi
    zeroHeight zeroHeight [] = false := by decide +kernel
example : intervalWithinUnit ⟨-1, 1, by norm_num⟩ = true := by decide +kernel
example : intervalWithinUnit ⟨-2, 0, by norm_num⟩ = false := by decide +kernel
example : unitPoint.toGridPoint.Valid emptyMomentGrid := by
  exact unitPoint.valid_of_check
    (DirichletEndpointIntervals.prepare_valid (SharedTaylorIntervals.prepare_prepared 0) 1 (by decide))
    rfl (SharedTaylorIntervals.prepare_prepared 0) pi_mem_twiddlePi
    (by simpa [emptyMomentGrid, emptyMomentBase] using IntervalRat.mem_singleton 0)
    (by simpa [emptyMomentGrid, emptyMomentBase] using IntervalRat.mem_singleton 0)
    (coefficients := []) rfl (by decide +kernel)
example : ‖riemannZeta ((1 / 2 : ℂ) + unitPoint.toGridPoint.height emptyMomentGrid * I) -
    unitPoint.toGridPoint.value emptyMomentGrid‖ ≤ unitPoint.toGridPoint.error emptyMomentGrid := by
  exact unitPoint.norm_zeta_sub_value_le emptyMomentGrid_valid
    (DirichletEndpointIntervals.prepare_valid (SharedTaylorIntervals.prepare_prepared 0) 1 (by decide))
    rfl (SharedTaylorIntervals.prepare_prepared 0) pi_mem_twiddlePi
    (by simpa [emptyMomentGrid, emptyMomentBase] using IntervalRat.mem_singleton 0)
    (by simpa [emptyMomentGrid, emptyMomentBase] using IntervalRat.mem_singleton 0)
    (coefficients := []) rfl (by decide +kernel)

end

end PrimeFactorUnimodality.Tests
