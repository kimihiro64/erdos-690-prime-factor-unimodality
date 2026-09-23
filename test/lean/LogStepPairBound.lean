import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.Analysis.Complex.LogStep.PairBound

/-! # Exact interfaces and boundary cases for LogStepPairBound -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex MeasureTheory

example {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    2 / (9 / 4 + w.im ^ 2) ≤ (1 / (1 - w)).re + (1 / (1 + w)).re :=
  two_div_le_re_resolvent_pair hw

example {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    logNormStepIntegral w + logNormStepIntegral (-w) ≤
      16 * ((1 / (1 - w)).re + (1 / (1 + w)).re) := logNormStepIntegral_pair_le hw

example {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    logNormStepIntegral w ≤ 16 * ((1 / (1 - w)).re + (1 / (1 + w)).re) :=
  logNormStepIntegral_le_resolvent_pair hw

example : logNormStepIntegral (1 / 2 : ℂ) + logNormStepIntegral (-(1 / 2 : ℂ)) ≤
    16 * ((1 / (1 - (1 / 2 : ℂ))).re + (1 / (1 + (1 / 2 : ℂ))).re) :=
  logNormStepIntegral_pair_le (by norm_num)

example (v : ℝ) :
    logNormStepIntegral ((1 / 2 : ℂ) + v * I) +
      logNormStepIntegral (-((1 / 2 : ℂ) + v * I)) ≤
      16 * ((1 / (1 - ((1 / 2 : ℂ) + v * I))).re +
        (1 / (1 + ((1 / 2 : ℂ) + v * I))).re) :=
  logNormStepIntegral_pair_le (by norm_num)

end

end PrimeFactorUnimodality.Tests
