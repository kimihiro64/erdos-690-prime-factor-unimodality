import PrimeFactorUnimodality.Helpers.Analytic.PlattTimeAliasing
import PrimeFactorUnimodality.Helpers.Analytic.PlattWindowDerivatives
import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.DiscretePoisson

set_option autoImplicit false

/-! # The exact finite Poisson pair for the Gamma window

The actual time and frequency periodizations form a discrete Fourier pair
of every positive integer length. Centered representatives keep both grids
inside the domains of the proved alias bounds. All infinite sums are the
genuine window and transform sums, not independent formal coefficients.
-/

open scoped FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- Samples of the true window in the central time cell. -/
def plattTimeGrid (N k : ℕ) (t₀ h B : ℝ) (j : ZMod N) : ℂ :=
  plattWindowKernel k t₀ h ((j.valMinAbs : ℝ) * B / N)

/-- Samples of the true transform in the central frequency cell. -/
def plattFrequencyGrid (N k : ℕ) (t₀ h B : ℝ) (j : ZMod N) : ℂ :=
  𝓕 (plattWindowKernel k t₀ h) ((j.valMinAbs : ℝ) / B)

/-- All time aliases at the centered grid points. -/
def plattTimeAliasGrid (N k : ℕ) (t₀ h B : ℝ) (j : ZMod N) : ℂ :=
  plattTimePeriodization k t₀ h B ((j.valMinAbs : ℝ) * B / N)

/-- All frequency aliases, at spacing `N/B`. -/
def plattFrequencyAliasGrid (N k : ℕ) (t₀ h B : ℝ) (j : ZMod N) : ℂ :=
  plattFourierPeriodization k t₀ h (N / B) ((j.valMinAbs : ℝ) / B)

variable {N : ℕ}

/-- Each frequency column is a sample of the genuine derivative of the base transform. -/
theorem plattFrequencyGrid_eq_iteratedDeriv (k : ℕ) (t₀ B : ℝ) {h : ℝ}
    (hh : 0 < h) (j : ZMod N) :
    plattFrequencyGrid N k t₀ h B j =
      iteratedDeriv k (𝓕 (plattWindowKernel 0 t₀ h)) ((j.valMinAbs : ℝ) / B) := by
  rw [iteratedDeriv_fourier_plattWindowKernel_zero k t₀ hh]
  rfl

variable [NeZero N]

/-- Every residue sum of the true Fourier coefficients is the corresponding frequency alias. -/
theorem residueTsum_plattFourier_eq (k : ℕ) (t₀ h B : ℝ) :
    ZMod.residueTsum (N := N) (fun n : ℤ => 𝓕 (plattWindowKernel k t₀ h) ((n : ℝ) / B)) =
      plattFrequencyAliasGrid N k t₀ h B := by
  funext j
  rw [ZMod.residueTsum_eq_of_intCast _ j.valMinAbs j j.coe_valMinAbs]
  apply tsum_congr
  intro l
  refine congrArg (𝓕 (plattWindowKernel k t₀ h)) ?_
  push_cast
  ring

/-- The inverse finite transform is exactly the periodized window, with its factor `1/B`. -/
theorem plattTimeAliasGrid_eq_dft_neg (k : ℕ) {t₀ h B : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B) (j : ZMod N) :
    plattTimeAliasGrid N k t₀ h B j =
      ((B⁻¹ : ℝ) : ℂ) * ZMod.dft (plattFrequencyAliasGrid N k t₀ h B) (-j) := by
  have hs : Summable (fun n : ℤ => 𝓕 (plattWindowKernel k t₀ h) ((n : ℝ) / B)) := by
    simpa only [zero_add, div_eq_mul_inv] using
      summable_plattFourierPeriodization 1 k (by omega) ht₀ hh (A := B⁻¹) (u := 0)
        (inv_pos.mpr hB) (by simp only [abs_zero]; positivity)
  have he : ((j.valMinAbs : ℝ) * B / N) / B = (j.valMinAbs : ℝ) / N := by
    field_simp
  rw [plattTimeAliasGrid, plattTimePeriodization,
    tsum_plattWindowKernel_eq_fourier_series k ht₀ hh hB, he,
    ZMod.tsum_fourier_grid_eq_dft_neg (N := N) hs j.valMinAbs,
    ZMod.coe_valMinAbs, residueTsum_plattFourier_eq]

/-- The forward finite transform has the dual normalization `B/N`. -/
theorem plattFrequencyAliasGrid_eq_dft (k : ℕ) {t₀ h B : ℝ}
    (ht₀ : 0 ≤ t₀) (hh : 0 < h) (hB : 0 < B) (j : ZMod N) :
    plattFrequencyAliasGrid N k t₀ h B j =
      ((B / N : ℝ) : ℂ) * ZMod.dft (plattTimeAliasGrid N k t₀ h B) j := by
  have ht : plattTimeAliasGrid N k t₀ h B = fun j =>
      ((B⁻¹ : ℝ) : ℂ) * ZMod.dft (plattFrequencyAliasGrid N k t₀ h B) (-j) :=
    funext (plattTimeAliasGrid_eq_dft_neg k ht₀ hh hB)
  rw [ht, ZMod.dft_const_mul, ZMod.dft_comp_neg, ZMod.dft_dft]
  simp only [smul_eq_mul, neg_neg]
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  push_cast
  field_simp

end

end PrimeFactorUnimodality
