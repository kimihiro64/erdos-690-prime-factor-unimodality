import PrimeFactorUnimodality.Helpers.Analytic.PlattDiscreteError
import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaPoisson

set_option autoImplicit false

/-! # Finite inverse Fourier evaluation of the actual zeta window

Regrouping the genuine Poisson series supplies the exact finite inverse
transform of all frequency aliases. Approximate frequency inputs and DFT
rounding then contribute separate errors alongside both proved analytic
aliases. No numerical enclosure or sign is asserted by this transport.
-/

open scoped FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- Centered samples of the actual zeta transform. -/
def plattZetaFrequencyGrid (N k : ℕ) (t₀ h B : ℝ) (j : ZMod N) : ℂ :=
  𝓕 (plattZetaWindow k t₀ h) ((j.valMinAbs : ℝ) / B)

/-- Full frequency aliases at the dual period `N/B`. -/
def plattZetaFrequencyAliasGrid (N k : ℕ) (t₀ h B : ℝ) (j : ZMod N) : ℂ :=
  plattZetaFourierPeriodization k t₀ h (N / B) ((j.valMinAbs : ℝ) / B)

variable {N : ℕ} [NeZero N]

/-- The residue sums regroup the true Fourier coefficients, not formal approximations. -/
theorem residueTsum_plattZetaFourier_eq (k : ℕ) (t₀ h B : ℝ) :
    ZMod.residueTsum (N := N) (fun n : ℤ => 𝓕 (plattZetaWindow k t₀ h) ((n : ℝ) / B)) =
      plattZetaFrequencyAliasGrid N k t₀ h B := by
  funext j
  rw [ZMod.residueTsum_eq_of_intCast _ j.valMinAbs j j.coe_valMinAbs]
  apply tsum_congr
  intro l
  refine congrArg (𝓕 (plattZetaWindow k t₀ h)) ?_
  push_cast
  ring

/-- The actual time periodization is exactly the inverse finite transform of frequency aliases. -/
theorem plattZetaTimePeriodization_grid_eq_dft_neg (k : ℕ) {t₀ h B : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B) (j : ZMod N) :
    plattZetaTimePeriodization k t₀ h B ((j.valMinAbs : ℝ) * B / N) =
      ((B⁻¹ : ℝ) : ℂ) * ZMod.dft (plattZetaFrequencyAliasGrid N k t₀ h B) (-j) := by
  have hs : Summable (fun n : ℤ => 𝓕 (plattZetaWindow k t₀ h) ((n : ℝ) / B)) := by
    simpa only [zero_add, div_eq_mul_inv] using
      summable_plattZetaFourierPeriodization k ht₀ hh (inv_pos.mpr hB) 0
  have he : ((j.valMinAbs : ℝ) * B / N) / B = (j.valMinAbs : ℝ) / N := by field_simp
  rw [plattZetaTimePeriodization, tsum_plattZetaWindow_eq_fourier_series k ht₀ hh hB, he,
    ZMod.tsum_fourier_grid_eq_dft_neg (N := N) hs j.valMinAbs,
    ZMod.coe_valMinAbs, residueTsum_plattZetaFourier_eq]

/-- Each true frequency sample differs from its alias sum by the closed contour budget. -/
theorem norm_plattZetaFrequencyAliasGrid_sub_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h B : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B) (j : ZMod N) :
    ‖plattZetaFrequencyAliasGrid N k t₀ h B j - plattZetaFrequencyGrid N k t₀ h B j‖ ≤
      plattZetaFourierAliasBound m k t₀ h (N / B) ((N / B) / 2) := by
  apply norm_plattZetaFourierPeriodization_sub_le m k hm ht₀ hh
    (by have := NeZero.pos N; positivity)
  have ht := plattFrequencyGrid_mem_cell hB j
  linarith

/-- Finite input and rounding errors are added to both genuine analytic alias bounds. -/
theorem norm_approximate_plattZetaFrequency_dft_sub_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h B ε δ : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * ((k : ℝ) + 1) * h ^ 2 < B ^ 2)
    {q : ZMod N → ℂ} (hq : ∀ i, ‖q i - plattZetaFrequencyGrid N k t₀ h B i‖ ≤ ε)
    (j : ZMod N) {z : ℂ} (hz : ‖z - ZMod.dft q (-j)‖ ≤ δ) :
    ‖((B⁻¹ : ℝ) : ℂ) * z - plattZetaWindow k t₀ h ((j.valMinAbs : ℝ) * B / N)‖ ≤
      B⁻¹ * δ + (N / B) *
        (ε + plattZetaFourierAliasBound m k t₀ h (N / B) ((N / B) / 2)) +
        plattZetaTimeAliasBound k t₀ h B := by
  have ha (i : ZMod N) : ‖q i - plattZetaFrequencyAliasGrid N k t₀ h B i‖ ≤
      ε + plattZetaFourierAliasBound m k t₀ h (N / B) ((N / B) / 2) := by
    apply (norm_sub_le_norm_sub_add_norm_sub _ (plattZetaFrequencyGrid N k t₀ h B i) _).trans
    apply add_le_add (hq i)
    rw [norm_sub_rev]
    exact norm_plattZetaFrequencyAliasGrid_sub_le m k hm ht₀ hh hB i
  have hd := (norm_sub_le_norm_sub_add_norm_sub z (ZMod.dft q (-j))
    (ZMod.dft (plattZetaFrequencyAliasGrid N k t₀ h B) (-j))).trans
      (add_le_add hz (ZMod.norm_dft_sub_le ha (-j)))
  have he : ‖((B⁻¹ : ℝ) : ℂ) * z -
      plattZetaTimePeriodization k t₀ h B ((j.valMinAbs : ℝ) * B / N)‖ ≤
      B⁻¹ * δ + (N / B) *
        (ε + plattZetaFourierAliasBound m k t₀ h (N / B) ((N / B) / 2)) := by
    rw [plattZetaTimePeriodization_grid_eq_dft_neg k ht₀ hh hB, ← mul_sub, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
    exact (mul_le_mul_of_nonneg_left hd (inv_pos.mpr hB).le).trans_eq (by ring)
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (plattZetaTimePeriodization k t₀ h B ((j.valMinAbs : ℝ) * B / N)) _).trans
      (add_le_add he (norm_plattZetaTimePeriodization_sub_le k t₀ hh hB hk
        (plattTimeGrid_mem_cell hB j)))

end

end PrimeFactorUnimodality
