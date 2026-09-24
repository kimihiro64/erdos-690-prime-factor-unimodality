import PrimeFactorUnimodality.Helpers.Analytic.PlattDiscreteError

set_option autoImplicit false

/-! # Transport from approximate finite transforms to the actual Gamma transform

Input enclosures and finite-transform rounding errors contribute separately
from the proved analytic aliases. The transform approximation can be supplied
by the existing shared radix trace; no arithmetic method is built into this
analytic transport theorem.
-/

namespace PrimeFactorUnimodality

noncomputable section

variable {N : ℕ} [NeZero N]

/-- All input and transform errors are retained alongside both analytic alias bounds. -/
theorem norm_approximate_plattTimeGrid_dft_sub_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h B ε δ : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2)
    {q : ZMod N → ℂ} (hq : ∀ i, ‖q i - plattTimeGrid N k t₀ h B i‖ ≤ ε)
    (j : ZMod N) {z : ℂ} (hz : ‖z - ZMod.dft q j‖ ≤ δ) :
    ‖((B / N : ℝ) : ℂ) * z - plattFrequencyGrid N k t₀ h B j‖ ≤
      (B / N) * δ + B * ε + B * plattTimeAliasBound k h B +
        plattFourierAliasBound m k t₀ h (N / B) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hn : ‖((B / N : ℝ) : ℂ)‖ = B / N := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hB hN)]
  have hr : ‖((B / N : ℝ) : ℂ) * z - ((B / N : ℝ) : ℂ) * ZMod.dft q j‖ ≤
      (B / N) * δ := by
    rw [← mul_sub, norm_mul, hn]
    exact mul_le_mul_of_nonneg_left hz (div_pos hB hN).le
  have hi : ‖((B / N : ℝ) : ℂ) * ZMod.dft q j -
      ((B / N : ℝ) : ℂ) * ZMod.dft (plattTimeGrid N k t₀ h B) j‖ ≤ B * ε := by
    rw [← mul_sub, norm_mul, hn]
    calc
      _ ≤ (B / N) * ((N : ℝ) * ε) :=
        mul_le_mul_of_nonneg_left (ZMod.norm_dft_sub_le hq j) (div_pos hB hN).le
      _ = _ := by field_simp
  have hs := (norm_sub_le_norm_sub_add_norm_sub
    (((B / N : ℝ) : ℂ) * z) (((B / N : ℝ) : ℂ) * ZMod.dft q j)
    (((B / N : ℝ) : ℂ) * ZMod.dft (plattTimeGrid N k t₀ h B) j)).trans
      (add_le_add hr hi)
  have ht := (norm_sub_le_norm_sub_add_norm_sub (((B / N : ℝ) : ℂ) * z)
    (((B / N : ℝ) : ℂ) * ZMod.dft (plattTimeGrid N k t₀ h B) j)
    (plattFrequencyGrid N k t₀ h B j)).trans
      (add_le_add hs (norm_plattTimeGrid_dft_sub_le m k hm ht₀ hh hB hk j))
  simpa only [add_assoc] using ht

end

end PrimeFactorUnimodality
