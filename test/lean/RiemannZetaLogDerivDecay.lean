import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.RiemannZetaLogDerivDecay

/-! # Exact interfaces and boundary cases for the complete horizontal tail -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology
open ArithmeticFunction

example {σ : ℝ} {s : ℂ}
    (hσ : 1 < σ) (hs : σ ≤ s.re) :
    ‖logDeriv riemannZeta s‖ ≤ (2 : ℝ) ^ (σ - s.re) *
      ∑' n, ‖LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ : ℂ) n‖ := by
  exact norm_logDeriv_riemannZeta_le_two_rpow hσ hs

example {s : ℂ} (hs : 1 < s.re) :
    ContinuousAt (logDeriv riemannZeta) s := by
  exact continuousAt_logDeriv_riemannZeta hs

example (σ : ℝ) :
    IntegrableOn (fun x : ℝ => (2 : ℝ) ^ (σ - x) *
      ∑' n, ‖LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ : ℂ) n‖) (Ioi σ) := by
  exact integrableOn_riemannZetaLogDerivMajorant σ

example {σ : ℝ} (hσ : 1 < σ) (T : ℝ) :
    IntegrableOn (fun x : ℝ => logDeriv riemannZeta ((x : ℂ) + T * I)) (Ioi σ) := by
  exact integrableOn_logDeriv_riemannZeta_horizontal_Ioi hσ T

example (T : ℝ) : IntegrableOn (fun x : ℝ => logDeriv riemannZeta ((x : ℂ) + T * I))
    (Ioi 2) := integrableOn_logDeriv_riemannZeta_horizontal_Ioi (by norm_num) T

example : IntegrableOn (fun x : ℝ => (2 : ℝ) ^ (-1 - x) *
    ∑' n, ‖LSeries.term (fun k => (vonMangoldt k : ℂ)) (-1 : ℂ) n‖) (Ioi (-1)) := by
  simpa using integrableOn_riemannZetaLogDerivMajorant (-1)

example (T : ℝ) : ‖logDeriv riemannZeta ((2 : ℂ) + T * I)‖ ≤
    ∑' n, ‖LSeries.term (fun k => (vonMangoldt k : ℂ)) (2 : ℂ) n‖ := by
  simpa using norm_logDeriv_riemannZeta_le_two_rpow
    (σ := 2) (s := (2 : ℂ) + T * I) (by norm_num) (by norm_num)

end

end PrimeFactorUnimodality.Tests
