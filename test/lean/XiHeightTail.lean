import PrimeFactorUnimodality.Helpers.Analytic.XiHeightTailZero
import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanIntegral

/-! # Height-tail pairing, finite mass, and endpoint regressions

Check that conjugation retains multiplicity labels, the cutoff fiber is
finite, the zero-height boundary term is not silently removed, and the
unconditional mass and divided-integral bounds are available independently
of a numerical zero-counting theorem.
-/

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Real MeasureTheory Set

example (A : ℝ) (p : {p : RiemannXiDivisorZeroIndex // A ≤ (riemannXiDivisorZeroValue p).im}) :
    ((xiPositiveNegativeHeightEquiv A p).1).1.2.val = p.1.1.2.val := rfl

example (A : ℝ) : {p : RiemannXiDivisorZeroIndex | (riemannXiDivisorZeroValue p).im = A}.Finite :=
  finite_xi_divisor_im_eq A

example (H : ℝ) (p : RiemannXiDivisorZeroIndex) (hp : |(riemannXiDivisorZeroValue p).im| = H) :
    p ∉ xiLowHeightIndices H := by
  rw [mem_xiLowHeightIndices, hp]
  exact lt_irrefl H

example {H : ℝ} (hH : 0 < H) :
    xiHeightTail 0 H =
      (∑' p : {p : RiemannXiDivisorZeroIndex // H < (riemannXiDivisorZeroValue p).im},
        Real.reciprocalSquarePair 0 (riemannXiDivisorZeroValue p.1).im) +
      (xiOrdinateMultiplicity H : ℝ) * (2 / H ^ 2) := by
  rw [xiHeightTail_eq_strict_positive_add_boundary hH, abs_zero, zero_add]
  congr 1
  unfold Real.reciprocalSquarePair
  ring

example {H : ℝ} (hH : 0 < H) :
    xiHeightTail 0 H ≤ 2 * (1 + 1 / H ^ 2) *
      ((2 + Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 - xiLowReciprocalMass H) :=
  xiHeightTail_zero_le_reciprocal_mass hH

example {H : ℝ} (hH : 0 < H) :
    xiHeightTail 0 H ≤ 2 * (1 + 1 / H ^ 2) *
      ((2 + Real.eulerMascheroniConstant - Real.log (4 * π)) / 2) := by
  simpa only [sub_zero] using xiHeightTail_zero_le_of_finite_mass hH ∅
    (by simp) (B := 0) (by simp)

example {H : ℝ} (hH : 0 < H) : (∫ x : ℝ in Ioi H, 1 / x ^ 2) = 1 / H :=
  Real.integral_inv_sq_Ioi hH

example {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    (∫ x in Ioi H, Real.reciprocalSquarePair t (x + t) / (x + t)) ≤ 2 / (t * H) :=
  Real.integral_reciprocalSquarePair_div_add_le ht hH

example {t x y : ℝ} (ht : 0 ≤ t) (hx : t < x) (hxy : x ≤ y) :
    Real.reciprocalSquarePair t y ≤ Real.reciprocalSquarePair t x :=
  Real.antitoneOn_reciprocalSquarePair ht hx (hx.trans_le hxy) hxy

example {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    xiLehmanIntegralCorrection t H ≤
      4 * Real.log (t + H) * (1 / H ^ 2 + 1 / (H + 2 * t) ^ 2) + 4 / (t * H) :=
  xiLehmanIntegralCorrection_le ht hH

end

end PrimeFactorUnimodality.Tests
