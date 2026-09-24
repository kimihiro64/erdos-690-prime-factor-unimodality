import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaXi

set_option autoImplicit false

/-! # Certified signs from enclosed genuine Platt-window values

The complete evaluator error must be strictly smaller than the approximate
real part's magnitude. The negative xi normalization reverses each sign.
Endpoints may come from different centers and widths; only their actual
ordinates are compared. No sign or zero-count completeness is assumed.
-/

namespace PrimeFactorUnimodality

/-- A separated negative window approximation proves a positive actual xi value. -/
theorem xiCriticalLineValue_pos_of_platt_approx {t₀ h v ε : ℝ} {z : ℂ}
    (hz : ‖z - plattZetaWindow 0 t₀ h v‖ ≤ ε) (hmargin : z.re < -ε) :
    0 < xiCriticalLineValue (v + t₀) := by
  have he := (Complex.abs_re_le_norm (z - plattZetaWindow 0 t₀ h v)).trans hz
  rw [Complex.sub_re] at he
  have hl := (abs_le.mp he).1
  apply (mul_pos_iff_of_pos_left (plattZetaXiScale_pos t₀ h v)).mp
  rw [← neg_re_plattZetaWindow_eq_scaled_xi]
  linarith

/-- A separated positive window approximation proves a negative actual xi value. -/
theorem xiCriticalLineValue_neg_of_platt_approx {t₀ h v ε : ℝ} {z : ℂ}
    (hz : ‖z - plattZetaWindow 0 t₀ h v‖ ≤ ε) (hmargin : ε < z.re) :
    xiCriticalLineValue (v + t₀) < 0 := by
  have he := (Complex.abs_re_le_norm (z - plattZetaWindow 0 t₀ h v)).trans hz
  rw [Complex.sub_re] at he
  have hu := (abs_le.mp he).2
  have hp : 0 < plattZetaXiScale t₀ h v * -xiCriticalLineValue (v + t₀) := by
    rw [mul_neg, ← neg_re_plattZetaWindow_eq_scaled_xi, neg_neg]
    linarith
  have hn := (mul_pos_iff_of_pos_left (plattZetaXiScale_pos t₀ h v)).mp hp
  linarith

/-- Either orientation of certified endpoint margins supplies the existing genuine divisor label. -/
theorem exists_xi_index_of_platt_approx_signs {t₀ t₁ h₀ h₁ a b ε₀ ε₁ : ℝ} {z₀ z₁ : ℂ}
    (hab : a + t₀ < b + t₁)
    (ha : ‖z₀ - plattZetaWindow 0 t₀ h₀ a‖ ≤ ε₀)
    (hb : ‖z₁ - plattZetaWindow 0 t₁ h₁ b‖ ≤ ε₁)
    (hm : (ε₀ < z₀.re ∧ z₁.re < -ε₁) ∨ (z₀.re < -ε₀ ∧ ε₁ < z₁.re)) :
    ∃ p : RiemannXiDivisorZeroIndex, (riemannXiDivisorZeroValue p).re = 1 / 2 ∧
      (riemannXiDivisorZeroValue p).im ∈ Set.Ioo (a + t₀) (b + t₁) := by
  apply exists_xi_criticalLine_index_of_sign_change hab
  rcases hm with ⟨hp, hn⟩ | ⟨hn, hp⟩
  · exact mul_neg_of_neg_of_pos (xiCriticalLineValue_neg_of_platt_approx ha hp)
      (xiCriticalLineValue_pos_of_platt_approx hb hn)
  · exact mul_neg_of_pos_of_neg (xiCriticalLineValue_pos_of_platt_approx ha hn)
      (xiCriticalLineValue_neg_of_platt_approx hb hp)

end PrimeFactorUnimodality
