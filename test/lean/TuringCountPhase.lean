import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringCountPhase

/-! # Exact interfaces and boundary regressions for counting normalization -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter Set
open MeasureTheory

example {σ : ℝ} (hσ : (1 / 2 : ℝ) ≤ σ) (T : ℝ) :
    (VIntegral xiGammaLogDerivative σ 0 T).im -
      (HIntegral xiGammaLogDerivative (1 / 2) σ T).im =
        (xiGammaLog ((1 / 2 : ℂ) + T * I)).im := by
  exact PrimeFactorUnimodality.xiGamma_half_contour_eq_left hσ T

example {σ T : ℝ} (hσ : 1 < σ)
    (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    Real.pi * riemannZeta.N T = turingZetaArgument σ T + turingCountingPhase T := by
  exact PrimeFactorUnimodality.pi_mul_zeta_N_eq_turingArgument_add_phase hσ hT htop

example {σ τ T : ℝ} (hσ : 1 < σ) (hτ : 1 < τ)
    (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    turingZetaArgument σ T = turingZetaArgument τ T := by
  exact PrimeFactorUnimodality.turingZetaArgument_eq_of_regular hσ hτ hT htop

example : ContinuousOn turingCountingPhase (Ioi 0) := by
  exact PrimeFactorUnimodality.continuousOn_turingCountingPhase

example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable turingCountingPhase volume a b := by
  exact PrimeFactorUnimodality.intervalIntegrable_turingCountingPhase ha hab

example {T : ℝ} (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    turingZetaArgument 2 T = turingZetaArgument 3 T :=
  turingZetaArgument_eq_of_regular (by norm_num) (by norm_num) hT htop

example (p : RiemannXiDivisorZeroIndex) (hp : 0 < (riemannXiDivisorZeroValue p).im) :
    IntervalIntegrable turingCountingPhase volume (riemannXiDivisorZeroValue p).im
      ((riemannXiDivisorZeroValue p).im + 1) :=
  intervalIntegrable_turingCountingPhase hp (by linarith)

end

end PrimeFactorUnimodality.Tests
