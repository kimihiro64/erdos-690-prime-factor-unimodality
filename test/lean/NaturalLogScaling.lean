import PrimeFactorUnimodality.Helpers.Analytic.NaturalLogScaling

/-! # Scaled natural logarithms and rejection of invalid integer enclosures -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open LeanCert.Core

private def config : SharedTaylorIntervals := SharedTaylorIntervals.prepare 40
private def bounds : NatLogScaleRow := ⟨1, 1, 20⟩
private def target : IntervalRat := ⟨13862 / 1000, 13863 / 1000, by norm_num⟩

example : bounds.check config 1048576 target = true := by decide +kernel
example : Real.log (1048576 : ℝ) ∈ target :=
  bounds.log_mem_of_check (SharedTaylorIntervals.prepare_prepared 40) (by decide +kernel)

example : (NatLogScaleRow.mk 0 1 20).check config 1048576 target = false := by decide +kernel
example : (NatLogScaleRow.mk 2 1 20).check config 1048576 target = false := by decide +kernel
example : bounds.check config 1048575 target = false := by decide +kernel
example : bounds.check config 1048577 target = false := by decide +kernel
example : bounds.check config 0 target = false := by decide +kernel
example : bounds.check config 1048576 ⟨13, 13, by norm_num⟩ = false := by decide +kernel

end PrimeFactorUnimodality.Tests
