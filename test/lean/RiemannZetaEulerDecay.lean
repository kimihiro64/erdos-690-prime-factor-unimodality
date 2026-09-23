import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaEulerDecay

/-! # Exact interfaces and boundary tests for horizontal zeta logarithms -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex LSeries

open ArithmeticFunction

example {σ : ℝ} (hσ : 1 < σ) :
    (∑' n, ‖LSeries.term (fun n => (vonMangoldt n : ℂ) / Real.log n) (σ : ℂ) n‖) =
      Real.log ‖riemannZeta (σ : ℂ)‖ := by
  exact tsum_norm_riemannZetaEulerLog_terms hσ

example {σ : ℝ} {s : ℂ}
    (hσ : 1 < σ) (hs : σ ≤ s.re) :
    ‖riemannZetaEulerLog s‖ ≤ (2 : ℝ) ^ (σ - s.re) * Real.log ‖riemannZeta (σ : ℂ)‖ := by
  exact norm_riemannZetaEulerLog_le_two_rpow hσ hs

example {σ : ℝ} {s : ℂ}
    (hσ : 1 < σ) (hs : σ ≤ s.re) :
    |Real.log ‖riemannZeta s‖| ≤
      (2 : ℝ) ^ (σ - s.re) * Real.log ‖riemannZeta (σ : ℂ)‖ := by
  exact abs_log_norm_riemannZeta_le_two_rpow hσ hs


example : ‖riemannZetaEulerLog (2 : ℂ)‖ ≤ Real.log ‖riemannZeta (2 : ℂ)‖ := by
  simpa using norm_riemannZetaEulerLog_le_two_rpow
    (s := (2 : ℂ)) (by norm_num : (1 : ℝ) < 2) (by norm_num)

example {x T : ℝ} (hx : 2 ≤ x) :
    |Real.log ‖riemannZeta ((x : ℂ) - T * I)‖| ≤
      (2 : ℝ) ^ (2 - x) * Real.log ‖riemannZeta (2 : ℂ)‖ := by
  simpa using abs_log_norm_riemannZeta_le_two_rpow
    (s := (x : ℂ) - T * I) (by norm_num : (1 : ℝ) < 2) (by simpa using hx)

end

end PrimeFactorUnimodality.Tests
