import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import PrimeFactorUnimodality.Helpers.Analytic.PlattContourResidueNorm

set_option autoImplicit false

/-! # A finite exponential envelope for the actual Gamma-window transform

The two proved contour shifts give one symmetric majorant. Its distinguished
term bounds the displaced integral; each remaining term is a crossed residue.
The slowest contour rate and the larger Gaussian shift cost cover both signs,
without discarding the first-shift Gamma correction.
-/

open Finset
open scoped FourierTransform

namespace PrimeFactorUnimodality

noncomputable section

/-- The corrected scalar moment majorant is nonnegative on its proved domain. -/
theorem plattScalarCMajorant_nonneg (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) : 0 ≤ plattScalarCMajorant m k t₀ h := by
  have hb := norm_fourier_plattWindowKernel_le_right_shift m k hm ht₀ hh 0
  exact nonneg_of_mul_nonneg_right ((norm_nonneg _).trans hb) (Real.exp_pos _)

/-- Every residue has exactly exponential frequency dependence. -/
theorem plattContourResidueNorm_eq_zero_mul_exp (n k : ℕ) (t₀ h u : ℝ) :
    plattContourResidueNorm n k t₀ h u = plattContourResidueNorm n k t₀ h 0 *
      Real.exp ((2 * Real.pi * (2 * (n : ℝ) + 1 / 2)) * u) := by
  have he : 2 * Real.pi * u * (2 * (n : ℝ) + 1 / 2) =
      (2 * Real.pi * (2 * (n : ℝ) + 1 / 2)) * u := by ring
  simp only [plattContourResidueNorm, mul_zero, zero_mul, add_zero, he, Real.exp_add]
  ring

/-- Nonnegative coefficients for the contour term (`none`) and its residues (`some n`). -/
def plattFourierEnvelopeCoeff (m k : ℕ) (t₀ h : ℝ) : Option (Fin (m + 1)) → ℝ
  | none => plattNegativeGammaFactor m * plattScalarCMajorant m k t₀ h *
      Real.exp ((2 * (m : ℝ) + 3 / 2) ^ 2 / (2 * h ^ 2))
  | some n => 2 * Real.pi * plattContourResidueNorm n k t₀ h 0

/-- The contour rate and every crossed-residue rate. -/
def plattFourierEnvelopeRate (m : ℕ) : Option (Fin (m + 1)) → ℝ
  | none => 2 * Real.pi * (2 * (m : ℝ) + 1 / 2)
  | some n => 2 * Real.pi * (2 * (n : ℝ) + 1 / 2)

theorem plattFourierEnvelopeRate_pos (m : ℕ) (i : Option (Fin (m + 1))) :
    0 < plattFourierEnvelopeRate m i := by
  cases i <;> simp only [plattFourierEnvelopeRate] <;> positivity

theorem plattFourierEnvelopeCoeff_nonneg (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (i : Option (Fin (m + 1))) :
    0 ≤ plattFourierEnvelopeCoeff m k t₀ h i := by
  cases i with
  | none =>
    exact mul_nonneg (mul_nonneg (plattNegativeGammaFactor_nonneg m)
      (plattScalarCMajorant_nonneg m k hm ht₀ hh)) (Real.exp_pos _).le
  | some n =>
    simp only [plattFourierEnvelopeCoeff, ← norm_plattContourResidueValue]
    positivity

/-- Both signs of the genuine transform are bounded by the same finite exponential sum. -/
theorem norm_fourier_plattWindowKernel_le_envelope (m k : ℕ) (hm : 1 ≤ m)
    {t₀ h : ℝ} (ht₀ : 0 ≤ t₀) (hh : 0 < h) (u : ℝ) :
    ‖𝓕 (plattWindowKernel k t₀ h) u‖ ≤
      ∑ i : Option (Fin (m + 1)), plattFourierEnvelopeCoeff m k t₀ h i *
        Real.exp (-plattFourierEnvelopeRate m i * |u|) := by
  have hC := plattScalarCMajorant_nonneg m k hm ht₀ hh
  have hfactor : 1 ≤ plattNegativeGammaFactor m := by
    unfold plattNegativeGammaFactor
    split_ifs <;> norm_num
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hcost : (2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) ≤
      (2 * (m : ℝ) + 3 / 2) ^ 2 / (2 * h ^ 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  rw [Fintype.sum_option]
  simp only [plattFourierEnvelopeCoeff, plattFourierEnvelopeRate]
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu]
    apply (norm_fourier_plattWindowKernel_le_right_shift m k hm ht₀ hh u).trans
    apply le_add_of_le_of_nonneg _ (sum_nonneg fun n _ => by
      rw [← norm_plattContourResidueValue]
      positivity)
    have he : (2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) -
        2 * Real.pi * u * (2 * (m : ℝ) + 1 / 2) =
        (2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2) +
          -(2 * Real.pi * (2 * (m : ℝ) + 1 / 2)) * u := by ring
    rw [he, Real.exp_add]
    have hfc : plattScalarCMajorant m k t₀ h ≤
        plattNegativeGammaFactor m * plattScalarCMajorant m k t₀ h := by nlinarith
    calc
      _ = plattScalarCMajorant m k t₀ h *
          Real.exp ((2 * (m : ℝ) + 1 / 2) ^ 2 / (2 * h ^ 2)) *
            Real.exp (-(2 * Real.pi * (2 * (m : ℝ) + 1 / 2)) * u) := by ring
      _ ≤ _ := by gcongr
  · have hu' : u ≤ 0 := le_of_not_ge hu
    rw [abs_of_nonpos hu']
    apply (norm_fourier_plattWindowKernel_le_left_explicit m k hm ht₀ hh u).trans
    apply add_le_add
    · have he : (2 * (m : ℝ) + 3 / 2) ^ 2 / (2 * h ^ 2) +
          2 * Real.pi * u * (2 * (m : ℝ) + 3 / 2) =
          (2 * (m : ℝ) + 3 / 2) ^ 2 / (2 * h ^ 2) +
            (2 * Real.pi * (2 * (m : ℝ) + 3 / 2)) * u := by ring
      rw [he, Real.exp_add]
      have hr : (2 * Real.pi * (2 * (m : ℝ) + 3 / 2)) * u ≤
          -(2 * Real.pi * (2 * (m : ℝ) + 1 / 2)) * -u := by
        nlinarith [Real.pi_pos]
      calc
        _ = (plattNegativeGammaFactor m * plattScalarCMajorant m k t₀ h) *
            Real.exp ((2 * (m : ℝ) + 3 / 2) ^ 2 / (2 * h ^ 2)) *
              Real.exp ((2 * Real.pi * (2 * (m : ℝ) + 3 / 2)) * u) := by ring
        _ ≤ _ := by gcongr
    · rw [← Fin.sum_univ_eq_sum_range, mul_sum]
      apply sum_le_sum
      intro n hn
      rw [plattContourResidueNorm_eq_zero_mul_exp]
      have he : -(2 * Real.pi * (2 * (n : ℝ) + 1 / 2)) * -u =
          (2 * Real.pi * (2 * (n : ℝ) + 1 / 2)) * u := by ring
      rw [he]
      exact le_of_eq (by ring)

end

end PrimeFactorUnimodality
