import PrimeFactorUnimodality.Helpers.Analytic.PlattDiscretePoisson

set_option autoImplicit false

/-! # Errors of the finite Gamma-window transforms

The exact discrete Poisson pair transports the proved time and frequency
alias bounds to the transforms of the actual centered samples. Both DFT
normalizations and the contribution of every input error are retained.
-/

namespace PrimeFactorUnimodality

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The centered time grid stays within the cell of the time-alias theorem. -/
theorem plattTimeGrid_mem_cell {B : ℝ} (hB : 0 < B) (j : ZMod N) :
    |(j.valMinAbs : ℝ) * B / N| ≤ B / 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  rw [abs_div, abs_mul, abs_of_pos hB, abs_of_pos hN, div_le_iff₀ hN]
  have ht := mul_le_mul_of_nonneg_right (ZMod.abs_valMinAbs_real_le_half j) hB.le
  nlinarith

/-- The centered frequency grid stays within its dual half-period. -/
theorem plattFrequencyGrid_mem_cell {B : ℝ} (hB : 0 < B) (j : ZMod N) :
    |(j.valMinAbs : ℝ) / B| ≤ (N / B) / 2 := by
  rw [abs_div, abs_of_pos hB]
  have ht := div_le_div_of_nonneg_right (ZMod.abs_valMinAbs_real_le_half j) hB.le
  convert ht using 1
  ring

/-- Every actual time sample differs from its complete alias sum by the explicit time bound. -/
theorem norm_plattTimeAliasGrid_sub_le (k : ℕ) (t₀ : ℝ) {h B : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2) (j : ZMod N) :
    ‖plattTimeAliasGrid N k t₀ h B j - plattTimeGrid N k t₀ h B j‖ ≤
      plattTimeAliasBound k h B :=
  norm_plattTimePeriodization_sub_le k t₀ hh hB hk (plattTimeGrid_mem_cell hB j)

/-- Every true transform sample differs from its complete frequency alias by the contour bound. -/
theorem norm_plattFrequencyAliasGrid_sub_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h B : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B) (j : ZMod N) :
    ‖plattFrequencyAliasGrid N k t₀ h B j - plattFrequencyGrid N k t₀ h B j‖ ≤
      plattFourierAliasBound m k t₀ h (N / B) :=
  norm_plattFourierPeriodization_sub_le m k hm ht₀ hh
    (by have := NeZero.pos N; positivity) (plattFrequencyGrid_mem_cell hB j)

/-- The finite forward transform of true window samples approximates the true Fourier samples. -/
theorem norm_plattTimeGrid_dft_sub_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h B : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2) (j : ZMod N) :
    ‖((B / N : ℝ) : ℂ) * ZMod.dft (plattTimeGrid N k t₀ h B) j -
        plattFrequencyGrid N k t₀ h B j‖ ≤
      B * plattTimeAliasBound k h B + plattFourierAliasBound m k t₀ h (N / B) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hd := ZMod.norm_dft_sub_le (a := plattTimeGrid N k t₀ h B)
    (b := plattTimeAliasGrid N k t₀ h B) (ε := plattTimeAliasBound k h B) (fun i => by
    rw [norm_sub_rev]
    exact norm_plattTimeAliasGrid_sub_le k t₀ hh hB hk i) j
  have he : ‖((B / N : ℝ) : ℂ) * ZMod.dft (plattTimeGrid N k t₀ h B) j -
      plattFrequencyAliasGrid N k t₀ h B j‖ ≤ B * plattTimeAliasBound k h B := by
    rw [plattFrequencyAliasGrid_eq_dft k ht₀ hh hB, ← mul_sub, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hB hN)]
    calc
      _ ≤ (B / N) * ((N : ℝ) * plattTimeAliasBound k h B) :=
        mul_le_mul_of_nonneg_left hd (div_pos hB hN).le
      _ = _ := by field_simp
  exact (norm_sub_le_norm_sub_add_norm_sub _ (plattFrequencyAliasGrid N k t₀ h B j) _).trans
    (add_le_add he (norm_plattFrequencyAliasGrid_sub_le m k hm ht₀ hh hB j))

/-- The finite inverse transform likewise approximates the actual window samples. -/
theorem norm_plattFrequencyGrid_dft_neg_sub_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h B : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2) (j : ZMod N) :
    ‖((B⁻¹ : ℝ) : ℂ) * ZMod.dft (plattFrequencyGrid N k t₀ h B) (-j) -
        plattTimeGrid N k t₀ h B j‖ ≤
      (N / B) * plattFourierAliasBound m k t₀ h (N / B) + plattTimeAliasBound k h B := by
  have hd := ZMod.norm_dft_sub_le (a := plattFrequencyGrid N k t₀ h B)
    (b := plattFrequencyAliasGrid N k t₀ h B)
    (ε := plattFourierAliasBound m k t₀ h (N / B)) (fun i => by
    rw [norm_sub_rev]
    exact norm_plattFrequencyAliasGrid_sub_le m k hm ht₀ hh hB i) (-j)
  have he : ‖((B⁻¹ : ℝ) : ℂ) * ZMod.dft (plattFrequencyGrid N k t₀ h B) (-j) -
      plattTimeAliasGrid N k t₀ h B j‖ ≤
        (N / B) * plattFourierAliasBound m k t₀ h (N / B) := by
    rw [plattTimeAliasGrid_eq_dft_neg k ht₀ hh hB, ← mul_sub, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
    calc
      _ ≤ B⁻¹ * ((N : ℝ) * plattFourierAliasBound m k t₀ h (N / B)) :=
        mul_le_mul_of_nonneg_left hd (inv_pos.mpr hB).le
      _ = _ := by ring
  exact (norm_sub_le_norm_sub_add_norm_sub _ (plattTimeAliasGrid N k t₀ h B j) _).trans
    (add_le_add he (norm_plattTimeAliasGrid_sub_le k t₀ hh hB hk j))

end

end PrimeFactorUnimodality
