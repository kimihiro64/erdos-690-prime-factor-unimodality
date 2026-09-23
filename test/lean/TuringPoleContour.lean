import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringPoleContour

/-! # Exact interfaces and boundary regressions for counting normalization -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter Set
open MeasureTheory

example {T : ℝ} (hT : 0 < T) :
    Continuous (fun x : ℝ => log ((x : ℂ) + T * I - 1)) := by
  exact PrimeFactorUnimodality.continuous_turingPoleLog hT

example {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => 1 / ((x : ℂ) + T * I - 1)) volume a b := by
  exact PrimeFactorUnimodality.intervalIntegrable_turingPole hT a b

example {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    HIntegral (fun s => 1 / (s - 1)) a b T =
      log ((b : ℂ) + T * I - 1) - log ((a : ℂ) + T * I - 1) := by
  exact PrimeFactorUnimodality.HIntegral_turingPole_eq hT a b

example {σ T : ℝ} (hσ : (1 / 2 : ℝ) ≤ σ)
    (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    IntervalIntegrable (fun x : ℝ => logDeriv riemannZeta ((x : ℂ) + T * I))
      volume (1 / 2) σ := by
  exact PrimeFactorUnimodality.intervalIntegrable_turingZetaLogDeriv hσ hT htop

example {σ T : ℝ} (hσ : (1 / 2 : ℝ) ≤ σ)
    (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    HIntegral (logDeriv Backlund.zetaSurrogate) (1 / 2) σ T =
      (log ((σ : ℂ) + T * I - 1) - log ((1 / 2 : ℂ) + T * I - 1)) +
        HIntegral (logDeriv riemannZeta) (1 / 2) σ T := by
  exact PrimeFactorUnimodality.HIntegral_backlund_eq_pole_add_zeta hσ hT htop

example : IntervalIntegrable (fun x : ℝ => 1 / ((x : ℂ) + (1 : ℝ) * I - 1)) volume 0 2 :=
  intervalIntegrable_turingPole (by norm_num) 0 2

example {T : ℝ} (hT : 0 < T) (a : ℝ) : HIntegral (fun s => 1 / (s - 1)) a a T = 0 := by
  simpa using HIntegral_turingPole_eq hT a a

end

end PrimeFactorUnimodality.Tests
