import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaLogContinuity

/-! # Exact interfaces and boundary cases for the complete horizontal tail -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology
open ArithmeticFunction

example {T : ℝ} (hT : 0 < T)
    (a b : ℝ) :
    ContinuousAt (fun t : ℝ => ∫ x in a..b, Real.log ‖riemannZeta ((x : ℂ) + t * I)‖) T := by
  exact continuousAt_integral_log_norm_riemannZeta_horizontal hT a b

example (a b : ℝ) :
    ContinuousOn (fun t : ℝ => ∫ x in a..b, Real.log ‖riemannZeta ((x : ℂ) + t * I)‖)
      (Ioi 0) := by
  exact continuousOn_integral_log_norm_riemannZeta_horizontal a b

example {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    ContinuousAt (fun t : ℝ => ∫ x in b..a, Real.log ‖riemannZeta ((x : ℂ) + t * I)‖) T :=
  continuousAt_integral_log_norm_riemannZeta_horizontal hT b a

example (a : ℝ) : ContinuousAt
    (fun t : ℝ => ∫ x in a..a, Real.log ‖riemannZeta ((x : ℂ) + t * I)‖) 1 :=
  continuousAt_integral_log_norm_riemannZeta_horizontal (by norm_num) a a

end

end PrimeFactorUnimodality.Tests
