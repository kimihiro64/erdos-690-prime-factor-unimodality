import PrimeFactorUnimodality.Helpers.Analytic.PlattDiscreteApproximation
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RadixError

set_option autoImplicit false

/-! # Shared radix outputs enclose the genuine Gamma-window transform

The existing transform trace supplies its complete arithmetic error to the
analytic transport theorem. Positive-phase output index `j` corresponds to
the Fourier sample at `-j`; both signs and the `B/N` scale are explicit.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- A valid shared FFT trace, with enclosed window inputs, bounds each actual Fourier sample. -/
theorem norm_plattRadixApproximation_sub_le (m k : ℕ) (hm : 1 ≤ m) {n : ℕ}
    {t₀ h B ε : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * (k : ℝ) * h ^ 2 < B ^ 2)
    {q : Vector ℂ (2 ^ n)} {t : Fourier.RadixTrace n}
    (hq : ∀ i : ZMod (2 ^ n),
      ‖q[i.val]'(ZMod.val_lt i) - plattTimeGrid (2 ^ n) k t₀ h B i‖ ≤ ε)
    (ht : t.Valid (ZMod.stdAddChar (1 : ZMod (2 ^ n))) q) (j : ZMod (2 ^ n)) :
    ‖((B / (2 ^ n : ℕ) : ℝ) : ℂ) * t.values[j.val]'(ZMod.val_lt j) -
        plattFrequencyGrid (2 ^ n) k t₀ h B (-j)‖ ≤
      (B / (2 ^ n : ℕ)) * t.error + B * ε + B * plattTimeAliasBound k h B +
        plattFourierAliasBound m k t₀ h ((2 ^ n : ℕ) / B) := by
  apply norm_approximate_plattTimeGrid_dft_sub_le m k hm ht₀ hh hB hk hq (-j)
  rw [norm_sub_rev]
  have hs := ht.norm_radixTwo_sub_le (by simp [ZMod.stdAddChar_apply])
    ⟨j.val, ZMod.val_lt j⟩
  rw [ZMod.radixTwo_eq_dft] at hs
  simpa only [ZMod.natCast_zmod_val] using hs

end

end PrimeFactorUnimodality
