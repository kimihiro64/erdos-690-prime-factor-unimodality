import PrimeFactorUnimodality.Helpers.Analytic.TuringPoleContour
import PrimeFactorUnimodality.Helpers.Analytic.XiGammaContour

/-! # Exact phase normalization of the Turing counting argument

The Euler logarithm fixes the argument on the right-hand vertical line.
Removing the surrogate pole then gives the actual horizontal zeta argument.
The count equals this argument plus the shifted Gamma phase and the left
pole argument. No principal logarithm of zeta is used inside the strip.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory Set

/-- The continuously varied zeta argument in radians at a regular height. -/
def turingZetaArgument (σ T : ℝ) : ℝ :=
  (riemannZetaEulerLog ((σ : ℂ) + T * I)).im -
    (HIntegral (logDeriv riemannZeta) (1 / 2) σ T).im

/-- The exact smooth phase accompanying the positive zero count, in radians. -/
def turingCountingPhase (T : ℝ) : ℝ :=
  (xiGammaLog ((1 / 2 : ℂ) + T * I)).im + arg ((1 / 2 : ℂ) + T * I - 1)

/-- The Gamma half-contour is the left endpoint value of its fixed primitive. -/
theorem xiGamma_half_contour_eq_left {σ : ℝ} (hσ : (1 / 2 : ℝ) ≤ σ) (T : ℝ) :
    (VIntegral xiGammaLogDerivative σ 0 T).im -
      (HIntegral xiGammaLogDerivative (1 / 2) σ T).im =
        (xiGammaLog ((1 / 2 : ℂ) + T * I)).im := by
  rw [VIntegral_xiGammaLogDerivative_eq (by linarith : 0 < σ),
    HIntegral_xiGammaLogDerivative_eq (by norm_num) hσ, sub_im, sub_im,
    xiGammaLog_ofReal_im (by linarith : 0 < σ)]
  simp only [ofReal_div, ofReal_one, ofReal_ofNat]
  ring

/-- The strict positive count has exactly the Euler-normalized argument and smooth phase. -/
theorem pi_mul_zeta_N_eq_turingArgument_add_phase {σ T : ℝ} (hσ : 1 < σ)
    (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    Real.pi * riemannZeta.N T = turingZetaArgument σ T + turingCountingPhase T := by
  rw [pi_mul_zeta_N_eq_surrogate_gamma_contour hσ hT htop,
    VIntegral_backlund_logDeriv_eq hσ, sub_im, backlundRightLog_ofReal_im hσ,
    HIntegral_backlund_eq_pole_add_zeta (by linarith) hT htop,
    xiGamma_half_contour_eq_left (by linarith)]
  simp only [turingZetaArgument, turingCountingPhase, backlundRightLog, add_im, sub_im, log_im]
  ring

/-- Changing the right-hand anchor does not change the continuously varied argument. -/
theorem turingZetaArgument_eq_of_regular {σ τ T : ℝ} (hσ : 1 < σ) (hτ : 1 < τ)
    (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    turingZetaArgument σ T = turingZetaArgument τ T := by
  linarith [pi_mul_zeta_N_eq_turingArgument_add_phase hσ hT htop,
    pi_mul_zeta_N_eq_turingArgument_add_phase hτ hT htop]

/-- The phase is continuous throughout positive heights, with no exclusions for zeros. -/
theorem continuousOn_turingCountingPhase : ContinuousOn turingCountingPhase (Ioi 0) := by
  intro T hT
  apply ContinuousAt.continuousWithinAt
  have hg : ContinuousAt (fun t : ℝ => xiGammaLog ((1 / 2 : ℂ) + t * I)) T :=
    (hasDerivAt_xiGammaLog (by norm_num)).continuousAt.comp (by fun_prop)
  have hp : ContinuousAt (fun t : ℝ => arg ((1 / 2 : ℂ) + t * I - 1)) T :=
    (continuousAt_arg (Or.inr (by simpa using ne_of_gt hT))).comp (by fun_prop)
  exact (continuous_im.continuousAt.comp hg).add hp

/-- Every positive finite interval admits the exact smooth-phase integral. -/
theorem intervalIntegrable_turingCountingPhase {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable turingCountingPhase volume a b :=
  (continuousOn_turingCountingPhase.mono (fun _ ht => ha.trans_le ht.1)).intervalIntegrable_of_Icc hab

end

end PrimeFactorUnimodality
