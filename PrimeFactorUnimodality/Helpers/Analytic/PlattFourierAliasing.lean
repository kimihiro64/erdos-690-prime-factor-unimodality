import PrimeFactorUnimodality.Helpers.Analytic.PlattFourierEnvelope
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.ExponentialAliasing

set_option autoImplicit false

/-! # Explicit aliasing error for the Gamma-window Fourier transform

Every term of the proved contour envelope is summed geometrically. This
controls the actual integer periodization on the entire central cell and
proves convergence, retaining the full residue contribution.
-/

open scoped FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- The periodized transform, before any finite numerical truncation. -/
def plattFourierPeriodization (k : ℕ) (t₀ h A u : ℝ) : ℂ :=
  ∑' n : ℤ, 𝓕 (plattWindowKernel k t₀ h) (u + (n : ℝ) * A)

/-- An explicit finite expression for both omitted frequency tails. -/
def plattFourierAliasBound (m k : ℕ) (t₀ h A : ℝ) : ℝ :=
  2 * ∑ i : Option (Fin (m + 1)), plattFourierEnvelopeCoeff m k t₀ h i *
    (Real.exp (-plattFourierEnvelopeRate m i * A / 2) /
      (1 - Real.exp (-plattFourierEnvelopeRate m i * A)))

/-- The actual transform values are summable on every central-cell lattice. -/
theorem summable_plattFourierPeriodization (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h A u : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A) (hu : |u| ≤ A / 2) :
    Summable (fun n : ℤ => 𝓕 (plattWindowKernel k t₀ h) (u + (n : ℝ) * A)) :=
  Fourier.summable_lattice_of_finite_exp_bound
    (s := Finset.univ) (fun i _ => plattFourierEnvelopeCoeff_nonneg m k hm ht₀ hh i)
    (fun i _ => plattFourierEnvelopeRate_pos m i) hA hu
    (norm_fourier_plattWindowKernel_le_envelope m k hm ht₀ hh)

/-- Exact geometric tails bound the error in replacing the periodization by its central term. -/
theorem norm_plattFourierPeriodization_sub_le (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h A u : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A) (hu : |u| ≤ A / 2) :
    ‖plattFourierPeriodization k t₀ h A u - 𝓕 (plattWindowKernel k t₀ h) u‖ ≤
      plattFourierAliasBound m k t₀ h A :=
  Fourier.norm_periodization_sub_le_of_finite_exp_bound
    (s := Finset.univ) (fun i _ => plattFourierEnvelopeCoeff_nonneg m k hm ht₀ hh i)
    (fun i _ => plattFourierEnvelopeRate_pos m i) hA hu
    (norm_fourier_plattWindowKernel_le_envelope m k hm ht₀ hh)

/-- The finite aliasing bound is nonnegative on the admissible parameter domain. -/
theorem plattFourierAliasBound_nonneg (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h A : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hA : 0 < A) :
    0 ≤ plattFourierAliasBound m k t₀ h A := by
  unfold plattFourierAliasBound
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (plattFourierEnvelopeCoeff_nonneg m k hm ht₀ hh i)
  apply div_nonneg (Real.exp_pos _).le
  apply sub_nonneg.mpr
  apply Real.exp_le_one_iff.mpr
  nlinarith [plattFourierEnvelopeRate_pos m i]

end

end PrimeFactorUnimodality
