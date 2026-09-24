import PrimeFactorUnimodality.Helpers.Analytic.PlattTaylorRemainder

set_option autoImplicit false

/-! # Complete errors for finite Taylor columns and weighted sums

Approximate derivative columns retain every coefficient error. Finite
weighted sums retain the norm of every weight, before any separate bound
on the Dirichlet coefficients or their omitted infinite tail is applied.
-/

open Finset
open scoped FourierTransform Nat

namespace PrimeFactorUnimodality

noncomputable section

/-- Approximate derivative samples incur their full factorial-weighted error in the polynomial. -/
theorem norm_plattFourierTaylor_sub_approx_le (K k : ℕ) (t₀ h u w : ℝ)
    {q : ℕ → ℂ} {ε : ℕ → ℝ}
    (hq : ∀ r ∈ range K, ‖𝓕 (plattWindowKernel (k + r) t₀ h) u - q r‖ ≤ ε r) :
    ‖plattFourierTaylor K k t₀ h u w - ∑ r ∈ range K, (w ^ r / (r ! : ℝ)) • q r‖ ≤
      ∑ r ∈ range K, (|w| ^ r / (r ! : ℝ)) * ε r := by
  rw [plattFourierTaylor, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro r hr
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left (hq r hr) (by positivity)

/-- The true shifted transform is enclosed by the approximate finite polynomial plus both errors. -/
theorem norm_fourier_plattWindowKernel_sub_approx_taylor_le (K k : ℕ) (t₀ u w : ℝ)
    {h : ℝ} (hh : 0 < h) {q : ℕ → ℂ} {ε : ℕ → ℝ}
    (hq : ∀ r ∈ range K, ‖𝓕 (plattWindowKernel (k + r) t₀ h) u - q r‖ ≤ ε r) :
    ‖𝓕 (plattWindowKernel k t₀ h) (u + w) -
        ∑ r ∈ range K, (w ^ r / (r ! : ℝ)) • q r‖ ≤
      plattFourierTaylorBound K k h |w| +
        ∑ r ∈ range K, (|w| ^ r / (r ! : ℝ)) * ε r := by
  exact (norm_sub_le_norm_sub_add_norm_sub _ (plattFourierTaylor K k t₀ h u w) _).trans
    (add_le_add (norm_fourier_plattWindowKernel_sub_taylor_le K k t₀ u w hh)
      (norm_plattFourierTaylor_sub_approx_le K k t₀ h u w hq))

/-- A common cell radius bounds all Taylor errors in a finite weighted transform sum. -/
theorem norm_sum_fourier_plattWindowKernel_sub_taylor_le {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (u w : ι → ℝ) (K k : ℕ) (t₀ : ℝ)
    {h ξ : ℝ} (hh : 0 < h) (hw : ∀ j ∈ s, |w j| ≤ ξ) :
    ‖(∑ j ∈ s, c j * 𝓕 (plattWindowKernel k t₀ h) (u j + w j)) -
        ∑ j ∈ s, c j * plattFourierTaylor K k t₀ h (u j) (w j)‖ ≤
      (∑ j ∈ s, ‖c j‖) * plattFourierTaylorBound K k h ξ := by
  rw [← sum_sub_distrib, sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j hj
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_fourier_plattWindowKernel_sub_taylor_le_radius K k t₀ (u j) hh (hw j hj))
    (norm_nonneg _)

/-- Reordering the finite polynomial columns loses neither terms nor weight factors. -/
theorem sum_plattFourierTaylor_eq_columns {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (u w : ι → ℝ) (K k : ℕ) (t₀ h : ℝ) :
    (∑ j ∈ s, c j * plattFourierTaylor K k t₀ h (u j) (w j)) =
      ∑ r ∈ range K, ∑ j ∈ s,
        (w j ^ r / (r ! : ℝ)) • (c j * 𝓕 (plattWindowKernel (k + r) t₀ h) (u j)) := by
  simp only [plattFourierTaylor, mul_sum, ← mul_smul_comm]
  exact sum_comm

end

end PrimeFactorUnimodality
