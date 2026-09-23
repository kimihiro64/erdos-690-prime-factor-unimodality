import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.LogStep.LargeHeight

/-! # Exact interfaces and boundary cases for LogStepLargeHeight -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex MeasureTheory

example {w : ℂ} (hw : |w.re| ≤ 1 / 2) (hv : w.im ≠ 0)
    {x : ℝ} (hx : x ∈ Set.Icc 0 1) : logNormStep w x ≤ 2 / w.im ^ 2 :=
  logNormStep_le_inv_im_sq hw hv hx

example {w : ℂ} (hw : |w.re| ≤ 1 / 2) (hv : w.im ≠ 0) :
    logNormStepIntegral w ≤ 2 / w.im ^ 2 := logNormStepIntegral_le_inv_im_sq hw hv

example : logNormStepIntegral I ≤ 2 := by
  simpa using logNormStepIntegral_le_inv_im_sq (w := I) (by norm_num) (by norm_num)

example : logNormStepIntegral (-I) ≤ 2 := by
  simpa using logNormStepIntegral_le_inv_im_sq (w := -I) (by norm_num) (by norm_num)

example : logNormStepIntegral ((1 / 2 : ℂ) + 2 * I) ≤ 1 / 2 := by
  convert logNormStepIntegral_le_inv_im_sq (w := (1 / 2 : ℂ) + 2 * I)
    (by norm_num) (by norm_num) using 1 <;> norm_num

end

end PrimeFactorUnimodality.Tests
