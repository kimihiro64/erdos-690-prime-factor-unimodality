import PrimeFactorUnimodality.Helpers.Analytic.PlattFourierAliasing

set_option autoImplicit false

/-! # Frequency aliasing after the Dirichlet shifts

The offset may leave the central half-period. The error therefore uses the
actual margin to the nearest omitted translate, rather than silently keeping
the unshifted margin. All crossed residues remain in the finite bound.
-/

open scoped FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- The exact geometric envelope with an explicit available frequency margin. -/
def plattFourierAliasBoundWithMargin (m k : ℕ) (t₀ h A d : ℝ) : ℝ :=
  2 * ∑ i : Option (Fin (m + 1)), plattFourierEnvelopeCoeff m k t₀ h i *
    (Real.exp (-plattFourierEnvelopeRate m i * d) /
      (1 - Real.exp (-plattFourierEnvelopeRate m i * A)))

/-- The earlier central-cell formula is exactly the half-period specialization. -/
theorem plattFourierAliasBoundWithMargin_half (m k : ℕ) (t₀ h A : ℝ) :
    plattFourierAliasBoundWithMargin m k t₀ h A (A / 2) =
      plattFourierAliasBound m k t₀ h A := by
  simp only [plattFourierAliasBoundWithMargin, plattFourierAliasBound, mul_div_assoc]

/-- The actual Fourier periodization converges at every real offset. -/
theorem summable_plattFourierPeriodization_all (k : ℕ) {t₀ h A : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A) (u : ℝ) :
    Summable (fun n : ℤ => 𝓕 (plattWindowKernel k t₀ h) (u + (n : ℝ) * A)) :=
  Fourier.summable_lattice_of_finite_exp_bound_margin (s := Finset.univ)
    (fun i _ => plattFourierEnvelopeCoeff_nonneg 1 k (by omega) ht₀ hh i)
    (fun i _ => plattFourierEnvelopeRate_pos 1 i) hA (d := A - |u|) (by linarith)
    (norm_fourier_plattWindowKernel_le_envelope 1 k (by omega) ht₀ hh)

/-- The available margin controls the true error, even outside the central half-period. -/
theorem norm_plattFourierPeriodization_sub_le_margin (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h A u d : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A)
    (hu : |u| + d ≤ A) :
    ‖plattFourierPeriodization k t₀ h A u - 𝓕 (plattWindowKernel k t₀ h) u‖ ≤
      plattFourierAliasBoundWithMargin m k t₀ h A d :=
  Fourier.norm_periodization_sub_le_of_finite_exp_bound_margin
    (s := Finset.univ) (fun i _ => plattFourierEnvelopeCoeff_nonneg m k hm ht₀ hh i)
    (fun i _ => plattFourierEnvelopeRate_pos m i) hA hu
    (norm_fourier_plattWindowKernel_le_envelope m k hm ht₀ hh)

/-- A shift bounded by `D` reduces the half-period margin by exactly `D`. -/
theorem norm_plattFourierPeriodization_shift_sub_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h A u s D : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A)
    (hu : |u| ≤ A / 2) (hs : |s| ≤ D) :
    ‖plattFourierPeriodization k t₀ h A (u - s) -
        𝓕 (plattWindowKernel k t₀ h) (u - s)‖ ≤
      plattFourierAliasBoundWithMargin m k t₀ h A (A / 2 - D) := by
  apply norm_plattFourierPeriodization_sub_le_margin m k hm ht₀ hh hA
  have ht : |u - s| ≤ |u| + |s| := by simpa using abs_sub_le u 0 s
  linarith

end

end PrimeFactorUnimodality
