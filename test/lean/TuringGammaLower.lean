import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.Analytic.TuringGammaLower

/-! # Exact interfaces and boundary cases for the actual logarithmic-ratio chain -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Filter MeasureTheory Set

example {s : ℂ} (hs : 0 ≤ s.re) :
    -2 ≤ (xiGammaLogDerivative s).re := by
  exact PrimeFactorUnimodality.neg_two_le_re_xiGammaLogDerivative hs

example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (T : ℝ) :
    -2 * (b - a) ≤ (xiGammaLog ((b : ℂ) + T * I)).re -
      (xiGammaLog ((a : ℂ) + T * I)).re := by
  exact PrimeFactorUnimodality.xiGammaLog_horizontal_sub_re_ge ha hab T

example {s : ℂ} (hs : 0 < s.re) :
    -2 ≤ (xiGammaLog (s + 1)).re - (xiGammaLog s).re := by
  exact PrimeFactorUnimodality.xiGammaLog_unit_sub_re_ge hs

example {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s = (s - 1) * exp (xiGammaLog s) * riemannZeta s := by
  exact PrimeFactorUnimodality.riemannXi_eq_pole_mul_exp_xiGammaLog hs hs1

example {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) (hxi : riemannXi s ≠ 0) :
    Real.log ‖riemannXi s‖ = Real.log ‖s - 1‖ + (xiGammaLog s).re +
      Real.log ‖riemannZeta s‖ := by
  exact PrimeFactorUnimodality.log_norm_riemannXi_eq_pole_gamma_zeta hs hs1 hxi

example (T : ℝ) : -2 ≤ (xiGammaLogDerivative (T * I)).re :=
  neg_two_le_re_xiGammaLogDerivative (by simp)

example (T : ℝ) : -2 * ((1 : ℝ) - 1) ≤ (xiGammaLog ((1 : ℂ) + T * I)).re -
    (xiGammaLog ((1 : ℂ) + T * I)).re :=
  xiGammaLog_horizontal_sub_re_ge (a := 1) (b := 1) (by norm_num) le_rfl T

example : -2 ≤ (xiGammaLog (2 : ℂ)).re - (xiGammaLog (1 : ℂ)).re := by
  simpa only [show (1 : ℂ) + 1 = 2 by norm_num] using
    xiGammaLog_unit_sub_re_ge (s := 1) (by norm_num)

end

end PrimeFactorUnimodality.Tests
