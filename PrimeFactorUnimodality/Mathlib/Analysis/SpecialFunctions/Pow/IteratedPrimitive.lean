/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.ComplexDecay

/-! # Successive primitives of complex powers on a positive half-line

The denominator is the finite product `s(s+1)...(s+n)`. Each derivative
cancels its last factor. The norm of the same product is bounded below
by the corresponding power of the absolute imaginary part.
-/

namespace Complex

noncomputable section

/-- The denominator `s(s+1)...(s+n)` in successive primitives of `t^s/s`. -/
def cpowPrimitiveDenom (s : ℂ) (n : ℕ) : ℂ :=
  ∏ j ∈ Finset.range (n + 1), (s + j)

/-- The `n`-th primitive of `t^s/s`, normalized by its finite-product denominator. -/
def cpowPrimitive (s : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s + n) / cpowPrimitiveDenom s n

/-- At order zero the only factor is `s`. -/
theorem cpowPrimitiveDenom_zero (s : ℂ) : cpowPrimitiveDenom s 0 = s := by
  simp [cpowPrimitiveDenom]

/-- One more primitive adds the next linear factor. -/
theorem cpowPrimitiveDenom_succ (s : ℂ) (n : ℕ) :
    cpowPrimitiveDenom s (n + 1) = cpowPrimitiveDenom s n * (s + (n + 1 : ℕ)) := by
  exact Finset.prod_range_succ _ (n + 1)

/-- Nonzero linear factors give a nonzero primitive denominator. -/
theorem cpowPrimitiveDenom_ne_zero {s : ℂ} (hs : ∀ j : ℕ, s + j ≠ 0) (n : ℕ) :
    cpowPrimitiveDenom s n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ => hs j)

/-- The zeroth primitive is the original divided power. -/
theorem cpowPrimitive_zero (s : ℂ) (t : ℝ) : cpowPrimitive s 0 t = (t : ℂ) ^ s / s := by
  simp [cpowPrimitive, cpowPrimitiveDenom_zero]

/-- Each primitive is continuous on every positive closed half-line. -/
theorem continuousOn_cpowPrimitive {a : ℝ} (ha : 0 < a) (s : ℂ) (n : ℕ) :
    ContinuousOn (cpowPrimitive s n) (Set.Ici a) :=
  (continuousOn_ofReal_cpow_Ici ha (s + n)).div_const _

/-- Differentiating cancels the last factor of the denominator. -/
theorem hasDerivAt_cpowPrimitive_succ {s : ℂ} (hs : ∀ j : ℕ, s + j ≠ 0)
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (cpowPrimitive s (n + 1)) (cpowPrimitive s n t) t := by
  have hd := (hasStrictDerivAt_cpow_const (c := s + (n + 1 : ℕ))
    (ofReal_mem_slitPlane.mpr ht)).hasDerivAt
  have he : s + (n + 1 : ℕ) - 1 = s + n := by push_cast; ring
  apply (hd.div_const (cpowPrimitiveDenom s (n + 1))).comp_ofReal.congr_deriv
  rw [he, cpowPrimitiveDenom_succ]
  change (s + (n + 1 : ℕ)) * (t : ℂ) ^ (s + n) /
    (cpowPrimitiveDenom s n * (s + (n + 1 : ℕ))) = (t : ℂ) ^ (s + n) / _
  field_simp [hs (n + 1), cpowPrimitiveDenom_ne_zero hs n]
  exact mul_div_cancel_left₀ _ (hs (n + 1))

/-- Every linear factor has norm at least the absolute imaginary part. -/
theorem pow_abs_im_le_norm_cpowPrimitiveDenom (s : ℂ) (n : ℕ) :
    |s.im| ^ (n + 1) ≤ ‖cpowPrimitiveDenom s n‖ := by
  induction n with
  | zero => simpa only [zero_add, pow_one, cpowPrimitiveDenom_zero] using abs_im_le_norm s
  | succ n ih =>
    rw [cpowPrimitiveDenom_succ, norm_mul, pow_succ]
    have hb : |s.im| ≤ ‖s + (n + 1 : ℕ)‖ := by
      simpa only [add_im, natCast_im, add_zero] using abs_im_le_norm (s + (n + 1 : ℕ))
    exact mul_le_mul ih hb (abs_nonneg _) (norm_nonneg _)

/-- A nonreal exponent never meets a denominator pole after a natural shift. -/
theorem add_natCast_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) (j : ℕ) :
    s + j ≠ 0 := by
  intro he
  apply hs
  have hi := congrArg Complex.im he
  simpa only [add_im, natCast_im, add_zero, zero_im] using hi

end

end Complex
