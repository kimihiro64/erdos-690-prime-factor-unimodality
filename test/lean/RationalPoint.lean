import PrimeFactorUnimodality.Mathlib.Analysis.Complex.RationalPoint

/-! # Rational checks and exact interface regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Complex.RationalPoint

example (a b : RationalPoint) :
    (a.add b).toComplex = a.toComplex + b.toComplex := by
  exact Complex.RationalPoint.toComplex_add a b

example (a b : RationalPoint) :
    (a.sub b).toComplex = a.toComplex - b.toComplex := by
  exact Complex.RationalPoint.toComplex_sub a b

example (a b : RationalPoint) :
    (a.mul b).toComplex = a.toComplex * b.toComplex := by
  exact Complex.RationalPoint.toComplex_mul a b

example (a : RationalPoint) (e : ℚ) :
    a.normLE e = true ↔ ‖a.toComplex‖ ≤ (e : ℝ) := by
  exact Complex.RationalPoint.normLE_eq_true a e

example (a : RationalPoint) {z : ℂ} {x y e : ℝ}
    (hx : |z.re - (a.re : ℝ)| ≤ x) (hy : |z.im - (a.im : ℝ)| ≤ y)
    (he : 0 ≤ e) (hs : x ^ 2 + y ^ 2 ≤ e ^ 2) : ‖z - a.toComplex‖ ≤ e := by
  exact Complex.RationalPoint.norm_sub_le_of_component_bounds a hx hy he hs

example : (RationalPoint.mk 3 4).normLE 5 = true := by decide +kernel
example : (RationalPoint.mk 3 4).normLE (499 / 100) = false := by decide +kernel
example : (RationalPoint.mk 0 0).normLE (-1) = false := by decide +kernel
example : (RationalPoint.mk 0 1).mul ⟨0, 1⟩ = ⟨-1, 0⟩ := by decide +kernel
example : (RationalPoint.mk (1 / 3) (-2 / 5)).sub ⟨1 / 3, -2 / 5⟩ = ⟨0, 0⟩ := by decide +kernel

end

end PrimeFactorUnimodality.Tests
