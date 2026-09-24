import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaDiscreteApproximation
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.RadixError

set_option autoImplicit false

/-! # Shared inverse FFT output encloses the true zeta window

The existing checked radix trace supplies the arithmetic error to the
proved inverse Fourier transport. Its positive-phase output index `j`
corresponds to the actual time sample at `j`, with scale `1/B`.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The complete inverse-grid budget, including input errors and both analytic aliases. -/
def plattZetaGridError (m N k : ℕ) (t₀ h B ε δ : ℝ) : ℝ :=
  B⁻¹ * δ + (N / B) *
    (ε + plattZetaFourierAliasBound m k t₀ h (N / B) ((N / B) / 2)) +
    plattZetaTimeAliasBound k t₀ h B

/-- A valid shared FFT trace and enclosed frequency inputs bound every actual time sample. -/
theorem norm_plattZetaRadixApproximation_sub_le (m k : ℕ) (hm : 1 ≤ m) {n : ℕ}
    {t₀ h B ε : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B)
    (hk : 4 * ((k : ℝ) + 1) * h ^ 2 < B ^ 2)
    {q : Vector ℂ (2 ^ n)} {t : Fourier.RadixTrace n}
    (hq : ∀ i : ZMod (2 ^ n),
      ‖q[i.val]'(ZMod.val_lt i) - plattZetaFrequencyGrid (2 ^ n) k t₀ h B i‖ ≤ ε)
    (ht : t.Valid (ZMod.stdAddChar (1 : ZMod (2 ^ n))) q) (j : ZMod (2 ^ n)) :
    ‖((B⁻¹ : ℝ) : ℂ) * t.values[j.val]'(ZMod.val_lt j) -
        plattZetaWindow k t₀ h ((j.valMinAbs : ℝ) * B / (2 ^ n : ℕ))‖ ≤
      plattZetaGridError m (2 ^ n) k t₀ h B ε t.error := by
  apply norm_approximate_plattZetaFrequency_dft_sub_le m k hm ht₀ hh hB hk hq j
  rw [norm_sub_rev]
  have hs := ht.norm_radixTwo_sub_le (by simp [ZMod.stdAddChar_apply])
    ⟨j.val, ZMod.val_lt j⟩
  rw [ZMod.radixTwo_eq_dft] at hs
  simpa only [ZMod.natCast_zmod_val] using hs

end

end PrimeFactorUnimodality
