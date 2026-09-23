import PrimeFactorUnimodality.Helpers.Analytic.XiLowReciprocalNormBound

/-! # Reciprocal-norm mass regression checks

Exercise the exact window endpoints, height-ten counting envelope, complex
conjugation, same-height reflection, and the bound on the complete strict
low set. The upper real-part gap stays an explicit input.
-/

namespace PrimeFactorUnimodality.Tests

open MeasureTheory Set

example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ p ∈ xiHeightWindowIndices a b, 1 / (riemannXiDivisorZeroValue p).im) =
      (xiZeroCount b : ℝ) / b - (xiZeroCount a : ℝ) / a +
        ∫ t in Icc a b, (xiZeroCount t : ℝ) / t ^ 2 := sum_xi_inv_im_window_eq ha hab

example {a : ℝ} (ha : 0 < a) :
    (∑ p ∈ xiHeightWindowIndices a a, 1 / (riemannXiDivisorZeroValue p).im) = 0 := by
  rw [sum_xi_inv_im_window_eq ha le_rfl]
  simp

example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ p ∈ xiHeightWindowIndices a b, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      (xiZeroCount b : ℝ) / b - (xiZeroCount a : ℝ) / a +
        ∫ t in Icc a b, (xiZeroCount t : ℝ) / t ^ 2 :=
  sum_xi_reciprocal_norm_window_le ha hab

example : (xiZeroCount 10 : ℝ) ≤ xiReciprocalCountEnvelope 10 :=
  xiZeroCount_le_reciprocal_envelope le_rfl

example {t : ℝ} (ht : 0 < t) :
    HasDerivAt xiReciprocalCountPrimitive (xiReciprocalCountEnvelope t / t ^ 2) t :=
  hasDerivAt_xiReciprocalCountPrimitive ht

example {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in Icc a b, xiReciprocalCountEnvelope t / t ^ 2) =
      xiReciprocalCountPrimitive b - xiReciprocalCountPrimitive a :=
  integral_xiReciprocalCountEnvelope_div_sq ha hab

example {b : ℝ} (hb : 10 ≤ b) :
    (∑ p ∈ xiHeightWindowIndices 10 b, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      xiReciprocalNormWindowBound 10 b := sum_xi_reciprocal_norm_window_le_explicit le_rfl hb

example (p : RiemannXiDivisorZeroIndex) :
    ‖(1 : ℂ) / riemannXiDivisorZeroValue (riemannXiDivisorConjugation p)‖ =
      ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖ := norm_xi_reciprocal_conjugation p

example (p : RiemannXiDivisorZeroIndex) : (riemannXiDivisorZeroValue p).im ≠ 0 :=
  xi_divisor_im_ne_zero p

example (T : ℝ) :
    (∑ p ∈ xiLowHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      2 * ∑ p ∈ xiPositiveHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖ :=
  sum_xi_low_reciprocal_norm_le_twice_positive T

example {T δ : ℝ}
    (hg : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    {p : RiemannXiDivisorZeroIndex} (hp : p ∈ xiLowHeightIndices T) :
    δ ≤ (riemannXiDivisorZeroValue p).re := xi_low_re_ge_of_gap hg hp

example {T δ : ℝ} (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    {p : RiemannXiDivisorZeroIndex} (hp : p ∈ xiLowHeightIndices T) :
    ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖ ≤ 1 / δ := norm_xi_low_reciprocal_le hδ hg hp

example {a T δ : ℝ} (haT : a < T) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    (∑ p ∈ xiPositiveHeightIndices a, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      (xiZeroCount a : ℝ) / δ := sum_xi_positive_prefix_reciprocal_norm_le haT hδ hg

example {a T δ : ℝ} (ha : 10 ≤ a) (haT : a < T) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    (∑ p ∈ xiLowHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      xiLowReciprocalNormBound a T δ := sum_xi_low_reciprocal_norm_le_explicit ha haT hδ hg

example {a T δ : ℝ} (ha : 0 ≤ a) (haT : a < T) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ)
    {p : RiemannXiDivisorZeroIndex} (hp : p ∈ xiPositiveHeightIndices a) :
    ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖ ≤
      ((a + 1) / δ) * (1 / riemannXiDivisorZeroValue p).re :=
  norm_xi_positive_prefix_reciprocal_le_mass ha haT hδ hg hp

example {a T δ : ℝ} (ha : 0 ≤ a) (haT : a < T) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    (∑ p ∈ xiPositiveHeightIndices a, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      ((a + 1) / δ) * ((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2) :=
  sum_xi_positive_prefix_reciprocal_norm_le_mass ha haT hδ hg

example {T δ : ℝ} (hT : 10 < T) (hδ : 0 < δ)
    (hg : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    (∑ p ∈ xiPositiveHeightIndices 10, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      (11 / δ) * ((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2) := by
  simpa only [show (10 : ℝ) + 1 = 11 by norm_num] using
    sum_xi_positive_prefix_reciprocal_norm_le_mass (by norm_num) hT hδ hg

example (a T δ : ℝ) :
    xiLowReciprocalNormBound a T δ ≤
      2 * (xiReciprocalCountEnvelope a / δ + xiReciprocalNormWindowBound a T) :=
  xiLowReciprocalNormBound_le_counting a T δ

end PrimeFactorUnimodality.Tests
