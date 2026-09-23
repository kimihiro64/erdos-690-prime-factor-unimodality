import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringFiniteLogDerivative

/-! # Exact interfaces and boundary regressions for counting normalization -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter Set
open MeasureTheory

example {σ T : ℝ} (hT : 0 < T)
    (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ u ∈ Icc (T - r) (T + r),
      0 < u ∧ ∀ x ∈ Icc (1 / 2 : ℝ) σ, riemannZeta ((x : ℂ) + u * I) ≠ 0 := by
  exact PrimeFactorUnimodality.exists_turing_regular_rectangle hT htop

example {x T : ℝ} (hT : T ≠ 0)
    (hz : riemannZeta ((x : ℂ) + T * I) ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖riemannZeta ((x : ℂ) + t * I)‖)
      (-(logDeriv riemannZeta ((x : ℂ) + T * I)).im) T := by
  exact PrimeFactorUnimodality.hasDerivAt_turingHorizontalLog hT hz

example {σ T : ℝ} (hσ : (1 / 2 : ℝ) ≤ σ)
    (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    HasDerivAt (fun t : ℝ => ∫ x in (1 / 2 : ℝ)..σ,
      Real.log ‖riemannZeta ((x : ℂ) + t * I)‖)
      (-(HIntegral (logDeriv riemannZeta) (1 / 2) σ T).im) T := by
  exact PrimeFactorUnimodality.hasDerivAt_turingHorizontalLog_finite hσ hT htop

example {T : ℝ} (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    HasDerivAt (fun t : ℝ => ∫ x in (1 / 2 : ℝ)..2,
      Real.log ‖riemannZeta ((x : ℂ) + t * I)‖)
      (-(HIntegral (logDeriv riemannZeta) (1 / 2) 2 T).im) T :=
  hasDerivAt_turingHorizontalLog_finite (by norm_num) hT htop

example {T : ℝ} (hT : 0 < T) (htop : ∀ z : ℂ, z.im = T → riemannXi z ≠ 0) :
    HasDerivAt (fun t : ℝ => ∫ x in (1 / 2 : ℝ)..(1 / 2 : ℝ),
      Real.log ‖riemannZeta ((x : ℂ) + t * I)‖) 0 T := by
  simpa [HIntegral] using hasDerivAt_turingHorizontalLog_finite le_rfl hT htop

example : HasDerivAt (fun t : ℝ => Real.log ‖riemannZeta ((2 : ℂ) + t * I)‖)
    (-(logDeriv riemannZeta ((2 : ℂ) + (-1 : ℝ) * I)).im) (-1) :=
  hasDerivAt_turingHorizontalLog (by norm_num)
    (riemannZeta_ne_zero_of_one_le_re (by norm_num))

end

end PrimeFactorUnimodality.Tests
