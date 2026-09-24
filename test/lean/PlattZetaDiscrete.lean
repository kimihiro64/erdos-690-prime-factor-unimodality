import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaDiscreteApproximation
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaXi

/-! The actual finite inverse DFT reaches the genuine window and existing xi divisor witnesses. -/

open PrimeFactorUnimodality

example {N : ℕ} [NeZero N] (k : ℕ) {t₀ h B : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B) (j : ZMod N) :
    plattZetaTimePeriodization k t₀ h B ((j.valMinAbs : ℝ) * B / N) =
      ((B⁻¹ : ℝ) : ℂ) * ZMod.dft (plattZetaFrequencyAliasGrid N k t₀ h B) (-j) :=
  plattZetaTimePeriodization_grid_eq_dft_neg k ht₀ hh hB j

example {N : ℕ} [NeZero N] (m k : ℕ) (hm : 1 ≤ m) {t₀ h B ε δ : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * ((k : ℝ) + 1) * h ^ 2 < B ^ 2)
    {q : ZMod N → ℂ} (hq : ∀ i, ‖q i - plattZetaFrequencyGrid N k t₀ h B i‖ ≤ ε)
    (j : ZMod N) {z : ℂ} (hz : ‖z - ZMod.dft q (-j)‖ ≤ δ) :
    ‖((B⁻¹ : ℝ) : ℂ) * z - plattZetaWindow k t₀ h ((j.valMinAbs : ℝ) * B / N)‖ ≤
      B⁻¹ * δ + (N / B) *
        (ε + plattZetaFourierAliasBound m k t₀ h (N / B) ((N / B) / 2)) +
        plattZetaTimeAliasBound k t₀ h B :=
  norm_approximate_plattZetaFrequency_dft_sub_le m k hm ht₀ hh hB hk hq j hz

example (t₀ h v : ℝ) :
    -(plattZetaWindow 0 t₀ h v).re = plattZetaXiScale t₀ h v * xiCriticalLineValue (v + t₀) :=
  neg_re_plattZetaWindow_eq_scaled_xi t₀ h v

example : 0 < plattZetaXiScale (-1000) 0 0 := plattZetaXiScale_pos (-1000) 0 0

example {t₀ h a b : ℝ} (hab : a < b)
    (hsign : (plattZetaWindow 0 t₀ h a).re * (plattZetaWindow 0 t₀ h b).re < 0) :
    ∃ p : RiemannXiDivisorZeroIndex, (riemannXiDivisorZeroValue p).re = 1 / 2 ∧
      (riemannXiDivisorZeroValue p).im ∈ Set.Ioo (a + t₀) (b + t₀) :=
  exists_xi_index_of_plattZetaWindow_sign_change hab hsign
