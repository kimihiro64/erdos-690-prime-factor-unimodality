import PrimeFactorUnimodality.Helpers.Analytic.TuringCountIntegral
import PrimeFactorUnimodality.Helpers.Analytic.TuringFiniteLogDerivative
import PrimeFactorUnimodality.Helpers.Analytic.TuringHorizontalLog
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaLogTailDerivative

/-! # The derivative of the complete horizontal Turing integral

The finite horizontal derivative and the entire right-tail derivative
combine with the exact split identity. At every regular positive height,
the derivative is the Euler-normalized zeta argument. Almost everywhere
it is therefore the actual closed count minus its exact Gamma/pole phase.
Continuity through exceptional zero heights is a separate obligation.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

/-- The entire horizontal integral differentiates to the normalized argument at a regular height. -/
theorem hasDerivAt_turingHorizontalIntegral {σ T : ℝ} (hσ : 1 < σ) (hT : 0 < T)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    HasDerivAt turingHorizontalIntegral (turingZetaArgument σ T) T := by
  have hd := (hasDerivAt_turingHorizontalLog_finite (σ := σ) (by linarith) hT htop).add
    (hasDerivAt_integral_log_norm_riemannZeta_horizontal_Ioi hσ T)
  have he : turingHorizontalIntegral =ᶠ[𝓝 T] (fun t : ℝ =>
      (∫ x in (1 / 2 : ℝ)..σ, Real.log ‖riemannZeta ((x : ℂ) + t * I)‖) +
        ∫ x in Ioi σ, Real.log ‖riemannZeta ((x : ℂ) + t * I)‖) := by
    filter_upwards [eventually_gt_nhds hT] with t ht
    exact turingHorizontalIntegral_eq_split ht.ne' hσ
  have h := hd.congr_of_eventuallyEq he
  convert h using 1
  unfold turingZetaArgument
  ring

/-- The derivative equals the actual multiplicity count minus its smooth phase almost everywhere. -/
theorem ae_hasDerivAt_turingHorizontalIntegral :
    ∀ᵐ T : ℝ, 0 < T → HasDerivAt turingHorizontalIntegral
      (Real.pi * (xiZeroCount T : ℝ) - turingCountingPhase T) T := by
  filter_upwards [ae_xi_horizontal_nonzero,
    ae_turingZetaArgument_eq_count_sub_phase (by norm_num : (1 : ℝ) < 2)] with T htop he hT
  rw [← he hT]
  exact hasDerivAt_turingHorizontalIntegral (by norm_num) hT htop

/-- On a closed interval of regular positive heights, the complete integral is continuous. -/
theorem continuousOn_turingHorizontalIntegral_of_regular {a b : ℝ} (ha : 0 < a)
    (hreg : ∀ T ∈ Icc a b, ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    ContinuousOn turingHorizontalIntegral (Icc a b) := by
  intro T hT
  exact (hasDerivAt_turingHorizontalIntegral (by norm_num : (1 : ℝ) < 2)
    (ha.trans_le hT.1) (hreg T hT)).continuousAt.continuousWithinAt

end

end PrimeFactorUnimodality
