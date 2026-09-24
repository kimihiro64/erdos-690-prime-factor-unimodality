import PrimeFactorUnimodality.Helpers.Analytic.PlattRadixApproximation

/-! The actual finite window/transform pair and complete approximation error at arbitrary order. -/

open PrimeFactorUnimodality
open scoped FourierTransform

example {N : ℕ} [NeZero N] (k : ℕ) {t₀ h B : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B) (j : ZMod N) :
    plattTimeAliasGrid N k t₀ h B j =
      ((B⁻¹ : ℝ) : ℂ) * ZMod.dft (plattFrequencyAliasGrid N k t₀ h B) (-j) :=
  plattTimeAliasGrid_eq_dft_neg k ht₀ hh hB j

example (k : ℕ) {t₀ h B : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B) :
    plattFrequencyAliasGrid 1 k t₀ h B 0 =
      (B : ℂ) * plattTimeAliasGrid 1 k t₀ h B 0 := by
  have ht := plattFrequencyAliasGrid_eq_dft (N := 1) k ht₀ hh hB 0
  rw [ZMod.dft_apply, Fintype.sum_subsingleton _ (0 : ZMod 1)] at ht
  simpa using ht

example (k : ℕ) (t₀ h B : ℝ) : plattTimeGrid 4 k t₀ h B 3 =
    plattWindowKernel k t₀ h (-B / 4) := by
  rw [plattTimeGrid, show (3 : ZMod 4).valMinAbs = (-1 : ℤ) by decide]
  norm_num

example {N : ℕ} [NeZero N] (m k : ℕ) (hm : 1 ≤ m) {t₀ h B : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2) (j : ZMod N) :
    ‖((B / N : ℝ) : ℂ) * ZMod.dft (plattTimeGrid N k t₀ h B) j -
        plattFrequencyGrid N k t₀ h B j‖ ≤
      B * plattTimeAliasBound k h B + plattFourierAliasBound m k t₀ h (N / B) :=
  norm_plattTimeGrid_dft_sub_le m k hm ht₀ hh hB hk j

example {N : ℕ} [NeZero N] (m k : ℕ) (hm : 1 ≤ m) {t₀ h B ε δ : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2) {q : ZMod N → ℂ}
    (hq : ∀ i, ‖q i - plattTimeGrid N k t₀ h B i‖ ≤ ε) (j : ZMod N)
    {z : ℂ} (hz : ‖z - ZMod.dft q j‖ ≤ δ) :
    ‖((B / N : ℝ) : ℂ) * z - plattFrequencyGrid N k t₀ h B j‖ ≤
      (B / N) * δ + B * ε + B * plattTimeAliasBound k h B +
        plattFourierAliasBound m k t₀ h (N / B) :=
  norm_approximate_plattTimeGrid_dft_sub_le m k hm ht₀ hh hB hk hq j hz

example (m k n : ℕ) (hm : 1 ≤ m) {t₀ h B ε : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2)
    {q : Vector ℂ (2 ^ n)} {t : Fourier.RadixTrace n}
    (hq : ∀ i : ZMod (2 ^ n),
      ‖q[i.val]'(ZMod.val_lt i) - plattTimeGrid (2 ^ n) k t₀ h B i‖ ≤ ε)
    (ht : t.Valid (ZMod.stdAddChar (1 : ZMod (2 ^ n))) q) (j : ZMod (2 ^ n)) :
    ‖((B / (2 ^ n : ℕ) : ℝ) : ℂ) * t.values[j.val]'(ZMod.val_lt j) -
        plattFrequencyGrid (2 ^ n) k t₀ h B (-j)‖ ≤
      (B / (2 ^ n : ℕ)) * t.error + B * ε + B * plattTimeAliasBound k h B +
        plattFourierAliasBound m k t₀ h ((2 ^ n : ℕ) / B) :=
  norm_plattRadixApproximation_sub_le m k hm ht₀ hh hB hk hq ht j

example {N : ℕ} [NeZero N] (k : ℕ) (t₀ B : ℝ) {h : ℝ} (hh : 0 < h) (j : ZMod N) :
    plattFrequencyGrid N k t₀ h B j =
      iteratedDeriv k (𝓕 (plattWindowKernel 0 t₀ h)) ((j.valMinAbs : ℝ) / B) :=
  plattFrequencyGrid_eq_iteratedDeriv k t₀ B hh j
