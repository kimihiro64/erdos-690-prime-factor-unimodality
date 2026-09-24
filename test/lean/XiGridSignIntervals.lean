import PrimeFactorUnimodality.Helpers.Analytic.XiGridSignIntervals

/-! # Full grid-error interfaces and small rational boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open Fourier
open PrimeFactorUnimodality.XiGridSignData

example (s : XiGridSignData) (r : RationalGridRows) (d : ZetaGroupedBlock)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {P : IntervalRat} (hpi : Real.pi ∈ P)
    (sharedCap : ℚ)
    (he : s.point.toGridPoint.error (r.attach d) ≤
      ((s.tailCap + sharedCap + s.point.error : ℚ) : ℝ))
    (h : s.checkMargin r d.degree c P sharedCap = true) :
    if s.positive then
      s.point.toGridPoint.xiError (r.attach d) s.phaseError <
        s.point.toGridPoint.xiApprox (r.attach d) s.phase
    else s.point.toGridPoint.xiApprox (r.attach d) s.phase <
      -s.point.toGridPoint.xiError (r.attach d) s.phaseError := by
  exact PrimeFactorUnimodality.XiGridSignData.margin_of_check s r d hc hpi sharedCap he h

def sampleRows : RationalGridRows :=
  ⟨[0], fun _ _ => ⟨2, 0⟩, 0,
    ⟨fun n => Vector.replicate (2 ^ (n + 1)) ⟨1, 0⟩, fun _ => 0⟩,
    fun _ => .leaf ⟨2, 0⟩ (1 / 4)⟩
def samplePoint : RationalGridPoint := ⟨0, 0, ⟨3, 0⟩, 0⟩
def piBox : IntervalRat := ⟨3, 4, by norm_num⟩

def signPoint : XiGridSignData := ⟨samplePoint, 0, 0, 0, 5, 1, 0, true⟩
example : signPoint.checkMargin sampleRows 1 (SharedTaylorIntervals.prepare 0) piBox 0 = true :=
  by decide +kernel
example : ({signPoint with valueCap := 4}).checkMargin sampleRows 1
    (SharedTaylorIntervals.prepare 0) piBox 0 = false := by decide +kernel
example : ({signPoint with phaseError := -1}).checkMargin sampleRows 1
    (SharedTaylorIntervals.prepare 0) piBox 0 = false := by decide +kernel
example : ({signPoint with tailCap := 9 / 2}).checkMargin sampleRows 1
    (SharedTaylorIntervals.prepare 0) piBox 0 = false := by decide +kernel
example : ({signPoint with positive := false}).checkMargin sampleRows 1
    (SharedTaylorIntervals.prepare 0) piBox 0 = false := by decide +kernel
def negativeSign : XiGridSignData :=
  {signPoint with point := {samplePoint with correction := ⟨-7, 0⟩}, positive := false}
example : negativeSign.checkMargin sampleRows 1 (SharedTaylorIntervals.prepare 0) piBox 0 = true :=
  by decide +kernel
example : ({negativeSign with tailCap := 9 / 2}).checkMargin sampleRows 1
    (SharedTaylorIntervals.prepare 0) piBox 0 = false := by decide +kernel

example : ({signPoint with tailCap := 9 / 2}).checkProjectionMargin sampleRows 1
    (SharedTaylorIntervals.prepare 0) piBox 0 = true := by decide +kernel
example : ({negativeSign with tailCap := 9 / 2}).checkProjectionMargin sampleRows 1
    (SharedTaylorIntervals.prepare 0) piBox 0 = true := by decide +kernel
example : ({signPoint with valueCap := 0}).checkProjectionMargin sampleRows 1
    (SharedTaylorIntervals.prepare 0) piBox 0 = true := by decide +kernel
example : ({signPoint with phaseError := 7 / 5}).checkProjectionMargin sampleRows 1
    (SharedTaylorIntervals.prepare 0) piBox 0 = false := by decide +kernel
example : ({signPoint with phaseError := -1}).checkProjectionMargin sampleRows 1
    (SharedTaylorIntervals.prepare 0) piBox 0 = false := by decide +kernel
example : ({signPoint with tailCap := 5}).checkProjectionMargin sampleRows 1
    (SharedTaylorIntervals.prepare 0) piBox 0 = false := by decide +kernel
example : ({negativeSign with tailCap := 5}).checkProjectionMargin sampleRows 1
    (SharedTaylorIntervals.prepare 0) piBox 0 = false := by decide +kernel
example : ({signPoint with point := {samplePoint with error := 5}}).checkProjectionMargin
    sampleRows 1 (SharedTaylorIntervals.prepare 0) piBox 0 = false := by decide +kernel
example : signPoint.checkProjectionMargin sampleRows 1
    (SharedTaylorIntervals.prepare 0) piBox 5 = false := by decide +kernel
example : ({signPoint with tailCap := 9 / 2}).checkSignMargin sampleRows 1
    (SharedTaylorIntervals.prepare 0) piBox 0 = true := by decide +kernel

end

end PrimeFactorUnimodality.Tests
