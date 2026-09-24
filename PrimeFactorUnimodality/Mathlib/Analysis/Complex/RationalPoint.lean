/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

/-! # Exact rational complex arithmetic and computable norm checks

Squared-norm comparisons avoid square roots and preserve the complete
Euclidean error, rather than replacing it by a looser coordinate sum.
-/

namespace Complex

/-- A complex value whose two coordinates can be checked by exact rational arithmetic. -/
structure RationalPoint where
  re : ℚ
  im : ℚ
  deriving DecidableEq, Repr

namespace RationalPoint

/-- Interpretation as a complex number. -/
def toComplex (a : RationalPoint) : ℂ := ⟨a.re, a.im⟩

/-- Exact coordinatewise addition. -/
def add (a b : RationalPoint) : RationalPoint := ⟨a.re + b.re, a.im + b.im⟩

/-- Exact coordinatewise subtraction. -/
def sub (a b : RationalPoint) : RationalPoint := ⟨a.re - b.re, a.im - b.im⟩

/-- Exact Gaussian multiplication. -/
def mul (a b : RationalPoint) : RationalPoint :=
  ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

/-- A rational scalar as an exact complex point. -/
def ofRat (a : ℚ) : RationalPoint := ⟨a, 0⟩

/-- Exact rational inverse, with the same zero convention as complex inversion. -/
def inv (a : RationalPoint) : RationalPoint :=
  ⟨a.re / (a.re ^ 2 + a.im ^ 2), -a.im / (a.re ^ 2 + a.im ^ 2)⟩

/-- A reusable natural-power computation on exact rational complex points. -/
def pow (a : RationalPoint) : ℕ → RationalPoint
  | 0 => ofRat 1
  | n + 1 => (a.pow n).mul a

/-- Rational scalar interpretation agrees with the standard cast. -/
@[simp] theorem toComplex_ofRat (a : ℚ) : (ofRat a).toComplex = (a : ℂ) := by
  apply Complex.ext <;> simp [toComplex, ofRat]

/-- Rational addition agrees with complex addition. -/
@[simp] theorem toComplex_add (a b : RationalPoint) :
    (a.add b).toComplex = a.toComplex + b.toComplex := by
  apply Complex.ext <;> simp [toComplex, add]

/-- Rational subtraction agrees with complex subtraction. -/
@[simp] theorem toComplex_sub (a b : RationalPoint) :
    (a.sub b).toComplex = a.toComplex - b.toComplex := by
  apply Complex.ext <;> simp [toComplex, sub]

/-- Rational multiplication agrees with complex multiplication. -/
@[simp] theorem toComplex_mul (a b : RationalPoint) :
    (a.mul b).toComplex = a.toComplex * b.toComplex := by
  apply Complex.ext <;> simp [toComplex, mul, Complex.mul_re, Complex.mul_im]

/-- Exact inversion agrees even at zero. -/
@[simp] theorem toComplex_inv (a : RationalPoint) : a.inv.toComplex = a.toComplex⁻¹ := by
  apply Complex.ext <;> simp [toComplex, inv, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, pow_two]

/-- The natural-power computation agrees with complex exponentiation. -/
@[simp] theorem toComplex_pow (a : RationalPoint) (n : ℕ) :
    (a.pow n).toComplex = a.toComplex ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow, ih, pow_succ]

/-- A Boolean Euclidean norm check using only rational operations. -/
def normLE (a : RationalPoint) (e : ℚ) : Bool :=
  decide (0 ≤ e ∧ a.re ^ 2 + a.im ^ 2 ≤ e ^ 2)

/-- The executable squared-norm check is equivalent to the actual complex bound. -/
theorem normLE_eq_true (a : RationalPoint) (e : ℚ) :
    a.normLE e = true ↔ ‖a.toComplex‖ ≤ (e : ℝ) := by
  simp only [normLE, decide_eq_true_eq]
  have hs : ‖a.toComplex‖ ^ 2 = (a.re : ℝ) ^ 2 + (a.im : ℝ) ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, toComplex, pow_two]
  constructor
  · rintro ⟨he, hsq⟩
    have he' : (0 : ℝ) ≤ e := by exact_mod_cast he
    have hsq' : (a.re : ℝ) ^ 2 + (a.im : ℝ) ^ 2 ≤ (e : ℝ) ^ 2 := by exact_mod_cast hsq
    nlinarith [norm_nonneg a.toComplex]
  · intro h
    have he' := (norm_nonneg a.toComplex).trans h
    refine ⟨by exact_mod_cast he', ?_⟩
    have hsq' : (a.re : ℝ) ^ 2 + (a.im : ℝ) ^ 2 ≤ (e : ℝ) ^ 2 := by
      nlinarith [norm_nonneg a.toComplex]
    exact_mod_cast hsq'

/-- Independent coordinate bounds imply the full Euclidean error budget. -/
theorem norm_sub_le_of_component_bounds (a : RationalPoint) {z : ℂ} {x y e : ℝ}
    (hx : |z.re - (a.re : ℝ)| ≤ x) (hy : |z.im - (a.im : ℝ)| ≤ y)
    (he : 0 ≤ e) (hs : x ^ 2 + y ^ 2 ≤ e ^ 2) : ‖z - a.toComplex‖ ≤ e := by
  have hx0 := (abs_nonneg _).trans hx
  have hy0 := (abs_nonneg _).trans hy
  have hx2 := (sq_le_sq₀ (abs_nonneg _) hx0).2 hx
  have hy2 := (sq_le_sq₀ (abs_nonneg _) hy0).2 hy
  simp only [sq_abs] at hx2 hy2
  have hn : ‖z - a.toComplex‖ ^ 2 =
      (z.re - (a.re : ℝ)) ^ 2 + (z.im - (a.im : ℝ)) ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, toComplex, pow_two]
  nlinarith [norm_nonneg (z - a.toComplex)]

end RationalPoint

end Complex
