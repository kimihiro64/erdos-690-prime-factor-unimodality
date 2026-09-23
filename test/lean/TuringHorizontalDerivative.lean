import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringHorizontalDerivative

/-! # Exact interfaces and boundary cases for the complete horizontal tail -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

example {σ T : ℝ} (hσ : 1 < σ) (hT : 0 < T)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    HasDerivAt turingHorizontalIntegral (turingZetaArgument σ T) T := by
  exact PrimeFactorUnimodality.hasDerivAt_turingHorizontalIntegral hσ hT htop

example :
    ∀ᵐ T : ℝ, 0 < T → HasDerivAt turingHorizontalIntegral
      (Real.pi * (xiZeroCount T : ℝ) - turingCountingPhase T) T := by
  exact PrimeFactorUnimodality.ae_hasDerivAt_turingHorizontalIntegral

example {a b : ℝ} (ha : 0 < a)
    (hreg : ∀ T ∈ Icc a b, ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    ContinuousOn turingHorizontalIntegral (Icc a b) := by
  exact PrimeFactorUnimodality.continuousOn_turingHorizontalIntegral_of_regular ha hreg

example {T : ℝ} (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    HasDerivAt turingHorizontalIntegral (turingZetaArgument 2 T) T :=
  hasDerivAt_turingHorizontalIntegral (by norm_num) hT htop

example {T : ℝ} (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    HasDerivAt turingHorizontalIntegral
      (Real.pi * riemannZeta.N T - turingCountingPhase T) T := by
  have he := pi_mul_zeta_N_eq_turingArgument_add_phase (by norm_num : (1 : ℝ) < 2) hT htop
  have hd := hasDerivAt_turingHorizontalIntegral (by norm_num : (1 : ℝ) < 2) hT htop
  have ha : Real.pi * riemannZeta.N T - turingCountingPhase T = turingZetaArgument 2 T := by linarith
  rw [ha]
  exact hd

end

end PrimeFactorUnimodality.Tests
