import PrimeFactorUnimodality.Helpers.Analytic.TuringHorizontalLog
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaLogContinuity
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaLogTailDerivative

/-! # Continuity of the complete Turing integral through zero heights

The finite horizontal integral is continuous by compact meromorphic
factorization, including all zero ordinates. The entire infinite tail is
continuous by its proved derivative. Their exact splitting identity
therefore establishes continuity without a zero-free-height hypothesis.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

/-- The full horizontal logarithmic integral is continuous at every positive height. -/
theorem continuousAt_turingHorizontalIntegral {T : ℝ} (hT : 0 < T) :
    ContinuousAt turingHorizontalIntegral T := by
  have hc := (continuousAt_integral_log_norm_riemannZeta_horizontal hT (1 / 2) 2).add
    (continuous_integral_log_norm_riemannZeta_horizontal_Ioi
      (by norm_num : (1 : ℝ) < 2)).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hT] with t ht
  exact turingHorizontalIntegral_eq_split ht.ne' (by norm_num)

/-- No exceptional zero heights have to be removed from the continuity domain. -/
theorem continuousOn_turingHorizontalIntegral :
    ContinuousOn turingHorizontalIntegral (Ioi 0) :=
  fun _ ht => (continuousAt_turingHorizontalIntegral ht).continuousWithinAt

end

end PrimeFactorUnimodality
