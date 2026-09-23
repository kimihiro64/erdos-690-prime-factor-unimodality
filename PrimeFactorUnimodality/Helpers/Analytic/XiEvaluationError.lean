import PrimeFactorUnimodality.Helpers.Analytic.XiNormalizedCriticalLine

/-! # Rigorous propagation of phase and zeta evaluation errors to xi signs

The zeta evaluator and phase evaluator supply independent absolute errors.
The resulting real interval certifies the actual xi sign after removing
its strictly positive amplitude. No zero-location or RH premise is used.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex

/-- Absolute value and phase errors give an absolute normalized xi error. -/
theorem abs_xiNormalizedValue_sub_approx_le {t θ εζ εθ : ℝ} {w : ℂ}
    (hz : ‖riemannZeta ((1 / 2 : ℂ) + t * I) - w‖ ≤ εζ)
    (hθ : |turingCountingPhase t - θ| ≤ εθ) :
    |xiNormalizedValue t - (exp (I * θ) * w).re| ≤ εζ + ‖w‖ * εθ := by
  exact (abs_re_rotated_sub_le (turingCountingPhase t) θ
    (riemannZeta ((1 / 2 : ℂ) + t * I)) w).trans
      (add_le_add hz (mul_le_mul_of_nonneg_left hθ (norm_nonneg w)))

/-- A positive lower interval endpoint certifies a positive actual xi value. -/
theorem xiCriticalLineValue_pos_of_approx {t θ εζ εθ : ℝ} {w : ℂ}
    (hz : ‖riemannZeta ((1 / 2 : ℂ) + t * I) - w‖ ≤ εζ)
    (hθ : |turingCountingPhase t - θ| ≤ εθ)
    (hmargin : εζ + ‖w‖ * εθ < (exp (I * θ) * w).re) :
    0 < xiCriticalLineValue t := by
  apply (xiCriticalLineValue_pos_iff_normalized t).mpr
  have h := (abs_le.mp (abs_xiNormalizedValue_sub_approx_le hz hθ)).1
  linarith

/-- A negative upper interval endpoint certifies a negative actual xi value. -/
theorem xiCriticalLineValue_neg_of_approx {t θ εζ εθ : ℝ} {w : ℂ}
    (hz : ‖riemannZeta ((1 / 2 : ℂ) + t * I) - w‖ ≤ εζ)
    (hθ : |turingCountingPhase t - θ| ≤ εθ)
    (hmargin : (exp (I * θ) * w).re < -(εζ + ‖w‖ * εθ)) :
    xiCriticalLineValue t < 0 := by
  apply (xiCriticalLineValue_neg_iff_normalized t).mpr
  have h := (abs_le.mp (abs_xiNormalizedValue_sub_approx_le hz hθ)).2
  linarith

/-- Strictly separated approximate signs certify an actual critical-line zero. -/
theorem exists_xi_zero_of_approx_signs {a b θa θb εa εb δa δb : ℝ} {u v : ℂ}
    (hab : a < b)
    (ha : ‖riemannZeta ((1 / 2 : ℂ) + a * I) - u‖ ≤ εa)
    (hb : ‖riemannZeta ((1 / 2 : ℂ) + b * I) - v‖ ≤ εb)
    (hθa : |turingCountingPhase a - θa| ≤ δa)
    (hθb : |turingCountingPhase b - θb| ≤ δb)
    (hposa : εa + ‖u‖ * δa < (exp (I * θa) * u).re)
    (hnegb : (exp (I * θb) * v).re < -(εb + ‖v‖ * δb)) :
    ∃ t ∈ Set.Ioo a b, riemannXi ((1 / 2 : ℂ) + t * I) = 0 := by
  exact exists_xi_criticalLine_zero_of_sign_change hab
    (mul_neg_of_pos_of_neg (xiCriticalLineValue_pos_of_approx ha hθa hposa)
      (xiCriticalLineValue_neg_of_approx hb hθb hnegb))

end

end PrimeFactorUnimodality
