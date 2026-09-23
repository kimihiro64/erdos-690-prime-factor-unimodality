import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringHorizontalContinuity

/-! # Exact interfaces and boundary cases for the complete horizontal tail -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

example {T : ℝ} (hT : 0 < T) :
    ContinuousAt turingHorizontalIntegral T := by
  exact PrimeFactorUnimodality.continuousAt_turingHorizontalIntegral hT

example :
    ContinuousOn turingHorizontalIntegral (Ioi 0) := by
  exact PrimeFactorUnimodality.continuousOn_turingHorizontalIntegral

example {T : ℝ} (hT : 0 < T) : ContinuousAt turingHorizontalIntegral T :=
  continuousAt_turingHorizontalIntegral hT

example {a b : ℝ} (ha : 0 < a) : ContinuousOn turingHorizontalIntegral (Icc a b) :=
  continuousOn_turingHorizontalIntegral.mono (fun _ ht => ha.trans_le ht.1)

end

end PrimeFactorUnimodality.Tests
