import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaLogIntegral

/-! # Exact interfaces and boundary tests for horizontal zeta logarithms -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex LSeries

open ArithmeticFunction

open MeasureTheory Set

example {T : ℝ} (hT : T ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) volume a b := by
  exact intervalIntegrable_log_norm_riemannZeta_horizontal hT a b

example {c : ℝ} (hc : 1 < c) (T : ℝ) :
    ContinuousOn (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) (Ioi c) := by
  exact continuousOn_log_norm_riemannZeta_horizontal hc T

example {c : ℝ} (hc : 1 < c) (T : ℝ) :
    IntegrableOn (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) (Ioi c) := by
  exact integrableOn_log_norm_riemannZeta_horizontal_Ioi hc T

example {c : ℝ} (hc : 1 < c) (T : ℝ) :
    (∫ x in Ioi c, |Real.log ‖riemannZeta ((x : ℂ) + T * I)‖|) ≤
      Real.log ‖riemannZeta (c : ℂ)‖ / Real.log 2 := by
  exact integral_abs_log_norm_riemannZeta_horizontal_Ioi_le hc T

example {c : ℝ} (hc : 1 < c) (T : ℝ) :
    |∫ x in Ioi c, Real.log ‖riemannZeta ((x : ℂ) + T * I)‖| ≤
      Real.log ‖riemannZeta (c : ℂ)‖ / Real.log 2 := by
  exact abs_integral_log_norm_riemannZeta_horizontal_Ioi_le hc T

example {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (T : ℝ) :
    |∫ x in a..b, Real.log ‖riemannZeta ((x : ℂ) + T * I)‖| ≤
      Real.log ‖riemannZeta (a : ℂ)‖ / Real.log 2 := by
  exact abs_integral_log_norm_riemannZeta_horizontal_le ha hab T


example : IntervalIntegrable
    (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + (14 : ℝ) * I)‖) volume (1 / 2) 2 := by
  exact intervalIntegrable_log_norm_riemannZeta_horizontal (by norm_num) _ _

example : IntervalIntegrable
    (fun x : ℝ => Real.log ‖riemannZeta ((x : ℂ) + (-14 : ℝ) * I)‖) volume 2 (1 / 2) := by
  exact intervalIntegrable_log_norm_riemannZeta_horizontal (by norm_num) _ _

example : IntegrableOn (fun x : ℝ => Real.log ‖riemannZeta (x : ℂ)‖) (Set.Ioi (2 : ℝ)) := by
  simpa using integrableOn_log_norm_riemannZeta_horizontal_Ioi
    (by norm_num : (1 : ℝ) < 2) 0

example (T a : ℝ) :
    (∫ x in a..a, Real.log ‖riemannZeta ((x : ℂ) + T * I)‖) = 0 := by simp

example (T : ℝ) :
    |∫ x in (3 : ℝ)..2, Real.log ‖riemannZeta ((x : ℂ) + T * I)‖| ≤
      Real.log ‖riemannZeta (2 : ℂ)‖ / Real.log 2 := by
  rw [intervalIntegral.integral_symm, abs_neg]
  exact abs_integral_log_norm_riemannZeta_horizontal_le (by norm_num) (by norm_num) T

end

end PrimeFactorUnimodality.Tests
