import PrimeFactorUnimodality.Helpers.Analytic.PlattContourLeftShift

set_option autoImplicit false

/-! # Explicit real sizes of the crossed residues

The residue norms reduce exactly to factorials, powers, a square root and a
real exponential. The resulting transform bound is suitable for numerical
enclosure without evaluating Gamma at or near any pole.
-/

open scoped FourierTransform

namespace PrimeFactorUnimodality

/-- The real size of one residue, including its complete frequency dependence. -/
noncomputable def plattContourResidueNorm (n k : ℕ) (t₀ h u : ℝ) : ℝ :=
  2 * (2 * Real.pi) ^ k / (n.factorial : ℝ) *
    Real.sqrt (t₀ ^ 2 + (2 * (n : ℝ) + 1 / 2) ^ 2) ^ k *
    Real.exp (((2 * (n : ℝ) + 1 / 2) ^ 2 - t₀ ^ 2) / (2 * h ^ 2) +
      2 * Real.pi * u * (2 * (n : ℝ) + 1 / 2))

/-- Exact residue norm, not merely a bound imported from the printed formula. -/
theorem norm_plattContourResidueValue (n k : ℕ) (t₀ h u : ℝ) :
    ‖plattContourResidueValue n k t₀ h u‖ = plattContourResidueNorm n k t₀ h u := by
  have hp : ‖plattGammaPole n t₀‖ = Real.sqrt (t₀ ^ 2 + (2 * (n : ℝ) + 1 / 2) ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply, plattGammaPole_re, plattGammaPole_im]
    congr 1
    ring
  have he : ((Real.pi : ℂ) * (plattGammaPole n t₀ + (t₀ : ℂ)) / 4 -
      (plattGammaPole n t₀) ^ 2 / ((2 * h ^ 2 : ℝ) : ℂ) +
      ((-2 * Real.pi * u : ℝ) : ℂ) * Complex.I * plattGammaPole n t₀).re =
        ((2 * (n : ℝ) + 1 / 2) ^ 2 - t₀ ^ 2) / (2 * h ^ 2) +
          2 * Real.pi * u * (2 * (n : ℝ) + 1 / 2) := by
    simp only [pow_two, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.div_ofNat_re,
      Complex.div_ofReal_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, plattGammaPole_re, plattGammaPole_im]
    ring
  unfold plattContourResidueValue plattContourWeight plattContourResidueNorm
  simp only [norm_mul, norm_pow, norm_div, Complex.norm_exp, he, hp]
  norm_num [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos]
  ring

/-- Fully real negative-frequency decay bound with the exact finite residue contribution. -/
theorem norm_fourier_plattWindowKernel_le_left_explicit (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    ‖𝓕 (plattWindowKernel k t₀ h) u‖ ≤
      Real.exp ((2 * (m : ℝ) + 3 / 2) ^ 2 / (2 * h ^ 2) +
        2 * Real.pi * u * (2 * (m : ℝ) + 3 / 2)) *
        (plattNegativeGammaFactor m * plattScalarCMajorant m k t₀ h) +
      2 * Real.pi * ∑ n ∈ Finset.range (m + 1), plattContourResidueNorm n k t₀ h u := by
  simpa only [norm_plattContourResidueValue] using
    norm_fourier_plattWindowKernel_le_left_shift m k hm ht₀ hh u

end PrimeFactorUnimodality
