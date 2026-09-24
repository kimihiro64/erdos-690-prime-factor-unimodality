import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaRadixApproximation
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaSignTransport

/-! Inverse FFT outputs reach genuine xi signs, including cross-window zero brackets. -/

open PrimeFactorUnimodality

example (m : ℕ) (hm : 1 ≤ m) {n : ℕ} {t₀ h B ε : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B) (hk : 4 * h ^ 2 < B ^ 2)
    {q : Vector ℂ (2 ^ n)} {t : Fourier.RadixTrace n}
    (hq : ∀ i : ZMod (2 ^ n),
      ‖q[i.val]'(ZMod.val_lt i) - plattZetaFrequencyGrid (2 ^ n) 0 t₀ h B i‖ ≤ ε)
    (ht : t.Valid (ZMod.stdAddChar (1 : ZMod (2 ^ n))) q) (j : ZMod (2 ^ n))
    (hmargin : (((B⁻¹ : ℝ) : ℂ) * t.values[j.val]'(ZMod.val_lt j)).re <
      -plattZetaGridError m (2 ^ n) 0 t₀ h B ε t.error) :
    0 < xiCriticalLineValue ((j.valMinAbs : ℝ) * B / (2 ^ n : ℕ) + t₀) := by
  exact xiCriticalLineValue_pos_of_platt_approx
    (norm_plattZetaRadixApproximation_sub_le m 0 hm ht₀ hh hB (by simpa using hk) hq ht j) hmargin

example {t₀ t₁ h₀ h₁ a b ε₀ ε₁ : ℝ} {z₀ z₁ : ℂ}
    (hab : a + t₀ < b + t₁)
    (ha : ‖z₀ - plattZetaWindow 0 t₀ h₀ a‖ ≤ ε₀)
    (hb : ‖z₁ - plattZetaWindow 0 t₁ h₁ b‖ ≤ ε₁)
    (h₀ : ε₀ < z₀.re) (h₁ : z₁.re < -ε₁) :
    ∃ p : RiemannXiDivisorZeroIndex, (riemannXiDivisorZeroValue p).re = 1 / 2 ∧
      (riemannXiDivisorZeroValue p).im ∈ Set.Ioo (a + t₀) (b + t₁) :=
  exists_xi_index_of_platt_approx_signs hab ha hb (Or.inl ⟨h₀, h₁⟩)

example {t₀ t₁ h₀ h₁ a b ε₀ ε₁ : ℝ} {z₀ z₁ : ℂ}
    (hab : a + t₀ < b + t₁)
    (ha : ‖z₀ - plattZetaWindow 0 t₀ h₀ a‖ ≤ ε₀)
    (hb : ‖z₁ - plattZetaWindow 0 t₁ h₁ b‖ ≤ ε₁)
    (h₀ : z₀.re < -ε₀) (h₁ : ε₁ < z₁.re) :
    ∃ p : RiemannXiDivisorZeroIndex, (riemannXiDivisorZeroValue p).re = 1 / 2 ∧
      (riemannXiDivisorZeroValue p).im ∈ Set.Ioo (a + t₀) (b + t₁) :=
  exists_xi_index_of_platt_approx_signs hab ha hb (Or.inr ⟨h₀, h₁⟩)
