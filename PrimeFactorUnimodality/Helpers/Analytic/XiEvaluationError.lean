import PrimeFactorUnimodality.Helpers.Analytic.XiNormalizedCriticalLine

/-! # Rigorous propagation of phase and zeta evaluation errors to xi signs

The zeta evaluator and phase evaluator supply independent absolute errors.
The resulting real interval certifies the actual xi sign after removing
its strictly positive amplitude. No zero-location or RH premise is used.
For signs alone, exact reality permits any phase error below a quarter turn:
the rotated real part differs by a positive cosine factor, not an additive
phase error. The stronger sign test does not assert a stronger value enclosure.
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

/-- A coarse phase certificate suffices for positive signs without an additive phase penalty. -/
theorem xiCriticalLineValue_pos_of_projection {t θ ε : ℝ} {w : ℂ}
    (hz : ‖riemannZeta ((1 / 2 : ℂ) + t * I) - w‖ ≤ ε)
    (hθ : |turingCountingPhase t - θ| < Real.pi / 2)
    (hmargin : ε < (exp (I * θ) * w).re) : 0 < xiCriticalLineValue t := by
  apply (xiCriticalLineValue_pos_iff_normalized t).mpr
  have he := abs_re_rotated_sub_le θ θ (riemannZeta ((1 / 2 : ℂ) + t * I)) w
  simp only [sub_self, abs_zero, mul_zero, add_zero] at he
  have hl := (abs_le.mp (he.trans hz)).1
  have hp : 0 < (exp (I * θ) * riemannZeta ((1 / 2 : ℂ) + t * I)).re := by linarith
  rw [abs_sub_comm] at hθ
  exact (re_rotated_pos_iff_of_im_eq_zero (turingCountingPhase t) θ _
    (xiNormalizedComplex_im t) hθ).mp hp

/-- The same projection argument certifies negative signs using only the zeta error. -/
theorem xiCriticalLineValue_neg_of_projection {t θ ε : ℝ} {w : ℂ}
    (hz : ‖riemannZeta ((1 / 2 : ℂ) + t * I) - w‖ ≤ ε)
    (hθ : |turingCountingPhase t - θ| < Real.pi / 2)
    (hmargin : (exp (I * θ) * w).re < -ε) : xiCriticalLineValue t < 0 := by
  apply (xiCriticalLineValue_neg_iff_normalized t).mpr
  have he := abs_re_rotated_sub_le θ θ (riemannZeta ((1 / 2 : ℂ) + t * I)) w
  simp only [sub_self, abs_zero, mul_zero, add_zero] at he
  have hu := (abs_le.mp (he.trans hz)).2
  have hn : (exp (I * θ) * riemannZeta ((1 / 2 : ℂ) + t * I)).re < 0 := by linarith
  rw [abs_sub_comm] at hθ
  exact (re_rotated_neg_iff_of_im_eq_zero (turingCountingPhase t) θ _
    (xiNormalizedComplex_im t) hθ).mp hn

end

end PrimeFactorUnimodality
