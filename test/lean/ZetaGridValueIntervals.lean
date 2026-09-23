import PrimeFactorUnimodality.Helpers.Analytic.ZetaGridValueIntervals

/-! # Full grid-error interfaces and small rational boundary regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open LeanCert.Core
open Fourier
open PrimeFactorUnimodality.RationalGridRows

example (r : RationalGridRows) (d : ZetaGroupedBlock) (p : RationalGridPoint)
    {P : IntervalRat} (hpi : Real.pi ∈ P) :
    p.toGridPoint.value (r.attach d) ∈ r.valueInterval p P d.degree := by
  exact PrimeFactorUnimodality.RationalGridRows.mem_valueInterval r d p hpi

def sampleRows : RationalGridRows :=
  ⟨[0], fun _ _ => ⟨2, 0⟩, 0,
    ⟨fun n => Vector.replicate (2 ^ (n + 1)) ⟨1, 0⟩, fun _ => 0⟩,
    fun _ => .leaf ⟨2, 0⟩ (1 / 4)⟩
def samplePoint : RationalGridPoint := ⟨0, 0, ⟨3, 0⟩, 0⟩
def piBox : IntervalRat := ⟨3, 4, by norm_num⟩

example : sampleRows.valueInterval samplePoint piBox 2 = ComplexInterval.point ⟨5, 0⟩ :=
  by decide +kernel
example : sampleRows.valueInterval samplePoint piBox 0 = ComplexInterval.point ⟨3, 0⟩ :=
  by decide +kernel
def signedRows : RationalGridRows :=
  ⟨sampleRows.groups, sampleRows.coefficient, 1, sampleRows.twiddles,
    fun _ => .node (.leaf ⟨0, 0⟩ 0) (.leaf ⟨0, 0⟩ 0) #v[⟨2, 0⟩, ⟨7, 0⟩] 0 0⟩
example : signedRows.sampleCoefficient (-1) 0 = ⟨7, 0⟩ := by decide +kernel
example : signedRows.sampleCoefficient (-2) 0 = ⟨2, 0⟩ := by decide +kernel

end

end PrimeFactorUnimodality.Tests
