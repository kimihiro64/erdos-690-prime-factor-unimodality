import PrimeFactorUnimodality.Helpers.Analytic.DigammaHadamardIntegral
import PrimeFactorUnimodality.Helpers.Analytic.XiHadamardIntegral

/-! # Absolute decomposition of the weighted zeta logarithmic derivative

The exact xi/gamma logarithmic-derivative identity may be integrated
termwise: each of its four weighted terms is absolutely integrable.
A zero-integral weight cancels the constant involving `log pi`.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex MeasureTheory

/-- Separate xi, the pole at one, and shifted gamma inside the contour integral. -/
theorem integral_mul_neg_logDeriv_riemannZeta_eq
    {c C : ℝ} (hc : 1 < c) (hC : 0 ≤ C) {H : ℝ → ℂ} (hH : Integrable H)
    (hBound : ∀ t, ‖H t‖ ≤ C / ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2)
    (hZero : (∫ t : ℝ, H t) = 0) :
    (∫ t : ℝ, H t * (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
      riemannZeta ((c : ℂ) + (t : ℂ) * I))) =
      -(∫ t : ℝ, H t * logDeriv riemannXi ((c : ℂ) + (t : ℂ) * I)) +
      (∫ t : ℝ, H t / ((c : ℂ) + (t : ℂ) * I - 1)) +
      (1 / 2 : ℂ) * (∫ t : ℝ, H t * digamma (((c : ℂ) + (t : ℂ) * I) / 2 + 1)) := by
  have hxi := integrable_mul_logDeriv_riemannXi hc hC hH hBound
  have hp := integrable_div_vertical hH (ρ := 1) (by simpa using hc)
  have hg := integrable_mul_digamma_half_add_one (by linarith) hC hH hBound
  have hk := hH.mul_const ((1 / 2 : ℂ) * Real.log Real.pi)
  have hxin : Integrable (fun t : ℝ => -(H t * logDeriv riemannXi
      ((c : ℂ) + (t : ℂ) * I))) := hxi.neg
  have hxp : Integrable (fun t : ℝ => -(H t * logDeriv riemannXi ((c : ℂ) + (t : ℂ) * I)) +
      H t / ((c : ℂ) + (t : ℂ) * I - 1)) := hxi.neg.add hp
  have hxpk : Integrable (fun t : ℝ => -(H t * logDeriv riemannXi ((c : ℂ) + (t : ℂ) * I)) +
      H t / ((c : ℂ) + (t : ℂ) * I - 1) - H t * ((1 / 2 : ℂ) * Real.log Real.pi)) :=
    hxp.sub hk
  calc
    _ = ∫ t : ℝ, -(H t * logDeriv riemannXi ((c : ℂ) + (t : ℂ) * I)) +
        H t / ((c : ℂ) + (t : ℂ) * I - 1) - H t * ((1 / 2 : ℂ) * Real.log Real.pi) +
        (1 / 2 : ℂ) * (H t * digamma (((c : ℂ) + (t : ℂ) * I) / 2 + 1)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [neg_logDeriv_riemannZeta_eq_xi (by simpa using hc)]
      ring
    _ = _ := by
      rw [integral_add hxpk (hg.const_mul (1 / 2 : ℂ)),
        integral_sub hxp hk, integral_add hxin hp, integral_neg,
        integral_mul_const, hZero, zero_mul, sub_zero, integral_const_mul]

end

end PrimeFactorUnimodality
