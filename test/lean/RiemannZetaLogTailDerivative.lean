import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaLogTailDerivative

/-! # Exact interfaces and boundary cases for the complete horizontal tail -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology
open ArithmeticFunction

example {σ : ℝ}
    (hσ : 1 < σ) (T : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x in Ioi σ, Real.log ‖riemannZeta ((x : ℂ) + t * I)‖)
      (riemannZetaEulerLog ((σ : ℂ) + T * I)).im T := by
  exact hasDerivAt_integral_log_norm_riemannZeta_horizontal_Ioi hσ T

example {σ : ℝ} (hσ : 1 < σ) :
    Continuous (fun T : ℝ => ∫ x in Ioi σ, Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) := by
  exact continuous_integral_log_norm_riemannZeta_horizontal_Ioi hσ

example {σ : ℝ} (hσ : 1 < σ) (a b : ℝ) :
    (∫ t in a..b, (riemannZetaEulerLog ((σ : ℂ) + t * I)).im) =
      (∫ x in Ioi σ, Real.log ‖riemannZeta ((x : ℂ) + b * I)‖) -
        ∫ x in Ioi σ, Real.log ‖riemannZeta ((x : ℂ) + a * I)‖ := by
  exact integral_im_riemannZetaEulerLog_vertical hσ a b

example : HasDerivAt (fun t : ℝ => ∫ x in Ioi (2 : ℝ),
    Real.log ‖riemannZeta ((x : ℂ) + t * I)‖) 0 0 := by
  simpa only [ofReal_zero, zero_mul, add_zero, riemannZetaEulerLog_ofReal_im] using
    hasDerivAt_integral_log_norm_riemannZeta_horizontal_Ioi
    (by norm_num : (1 : ℝ) < 2) 0

example : HasDerivAt (fun t : ℝ => ∫ x in Ioi (2 : ℝ),
    Real.log ‖riemannZeta ((x : ℂ) + t * I)‖)
      (riemannZetaEulerLog ((2 : ℂ) + (-1 : ℝ) * I)).im (-1) :=
  hasDerivAt_integral_log_norm_riemannZeta_horizontal_Ioi (σ := 2) (by norm_num) (-1)

example (a b : ℝ) : (∫ t in b..a, (riemannZetaEulerLog ((2 : ℂ) + t * I)).im) =
    (∫ x in Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + a * I)‖) -
      ∫ x in Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + b * I)‖ :=
  integral_im_riemannZetaEulerLog_vertical (σ := 2) (by norm_num) b a

end

end PrimeFactorUnimodality.Tests
