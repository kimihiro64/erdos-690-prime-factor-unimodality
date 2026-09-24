import PrimeFactorUnimodality.Helpers.Analytic.PlattWindowDerivatives
import PrimeFactorUnimodality.Mathlib.Analysis.Calculus.TaylorBound

set_option autoImplicit false

/-! # Taylor truncation of the genuine Gamma-window transform

The finite polynomial uses the actual weighted Fourier transforms. Their
proved derivative identities and uniform Gaussian moments give the complete
remainder with the factorial denominator, for either sign of the shift and
every truncation order, including zero.
-/

open Finset
open scoped ContDiff FourierTransform Nat

namespace PrimeFactorUnimodality

noncomputable section

/-- The first `K` actual derivative coefficients at the center frequency. -/
def plattFourierTaylor (K k : ℕ) (t₀ h u w : ℝ) : ℂ :=
  ∑ r ∈ range K, (w ^ r / (r ! : ℝ)) • 𝓕 (plattWindowKernel (k + r) t₀ h) u

/-- The closed Gaussian-moment remainder budget on a shift radius. -/
def plattFourierTaylorBound (K k : ℕ) (h ξ : ℝ) : ℝ :=
  plattWindowL1Bound (k + K) h * ξ ^ K / (K ! : ℝ)

/-- The actual integral-norm bound is nonnegative on the positive-width domain. -/
theorem plattWindowL1Bound_nonneg (k : ℕ) {h : ℝ} (hh : 0 < h) :
    0 ≤ plattWindowL1Bound k h :=
  (norm_nonneg _).trans (norm_fourier_plattWindowKernel_le k 0 0 hh)

/-- The true Taylor remainder for every signed shift, with the full factorial denominator. -/
theorem norm_fourier_plattWindowKernel_sub_taylor_le (K k : ℕ) (t₀ u w : ℝ)
    {h : ℝ} (hh : 0 < h) :
    ‖𝓕 (plattWindowKernel k t₀ h) (u + w) - plattFourierTaylor K k t₀ h u w‖ ≤
      plattFourierTaylorBound K k h |w| := by
  cases K with
  | zero =>
    simpa only [plattFourierTaylor, range_zero, sum_empty, sub_zero,
      plattFourierTaylorBound, Nat.add_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, mul_one, div_one] using norm_fourier_plattWindowKernel_le k t₀ (u + w) hh
  | succ K =>
    have hf : ContDiff ℝ (K + 1 : ℕ) (𝓕 (plattWindowKernel k t₀ h)) :=
      (contDiff_fourier_plattWindowKernel k t₀ hh).of_le (by simp)
    have ht := norm_sub_sum_taylor_le (a := u) (x := u + w) hf
      (C := plattWindowL1Bound (k + (K + 1)) h)
      (fun y _ => norm_iteratedDeriv_fourier_plattWindowKernel_le (K + 1) k t₀ y hh)
    have hd (r : ℕ) := iteratedDeriv_fourier_plattWindowKernel r k t₀ hh
    simpa only [add_sub_cancel_left, hd,
      plattFourierTaylor, plattFourierTaylorBound] using ht

/-- One uniform radius budget covers both signs and every point in the frequency cell. -/
theorem norm_fourier_plattWindowKernel_sub_taylor_le_radius (K k : ℕ) (t₀ u : ℝ)
    {h w ξ : ℝ} (hh : 0 < h) (hw : |w| ≤ ξ) :
    ‖𝓕 (plattWindowKernel k t₀ h) (u + w) - plattFourierTaylor K k t₀ h u w‖ ≤
      plattFourierTaylorBound K k h ξ := by
  apply (norm_fourier_plattWindowKernel_sub_taylor_le K k t₀ u w hh).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg w) hw K)
    (plattWindowL1Bound_nonneg (k + K) hh)

/-- The radius bound itself is nonnegative for every nonnegative radius. -/
theorem plattFourierTaylorBound_nonneg (K k : ℕ) {h ξ : ℝ} (hh : 0 < h) (hξ : 0 ≤ ξ) :
    0 ≤ plattFourierTaylorBound K k h ξ := by
  exact div_nonneg (mul_nonneg (plattWindowL1Bound_nonneg (k + K) hh)
    (pow_nonneg hξ K)) (by positivity)

end

end PrimeFactorUnimodality
