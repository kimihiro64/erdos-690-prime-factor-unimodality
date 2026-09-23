/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.Analysis.Calculus.Deriv.ForwardDiff
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageLocal

/-! # Iterated averages as forward differences of primitives

For any sequence of successive primitives on a half-line, the `n`-fold
average equals its `n`-th forward difference divided by the step to power
`n`. This is an exact FTC identity for every natural order.
-/

open Complex Function MeasureTheory Set

namespace intervalIntegral

noncomputable section

/-- Repeated FTC expresses an iterated average as a difference of its higher primitive. -/
theorem iteratedBoxAverageComplex_eq_fwdDiff {a h : ℝ} (hh : 0 < h)
    (F : ℕ → ℝ → ℂ) (hF : ∀ n, ContinuousOn (F n) (Ici a))
    (hderiv : ∀ n t, a ≤ t → HasDerivAt (F (n + 1)) (F n t) t)
    (n : ℕ) {x : ℝ} (hx : a ≤ x) :
    iteratedBoxAverageComplex h n (F 0) x =
      ((h : ℂ) ^ n)⁻¹ * ((fwdDiff h)^[n] (F n)) x := by
  induction n generalizing x with
  | zero => simp [iteratedBoxAverageComplex, iteratedBoxAverage]
  | succ n ih =>
    rw [iteratedBoxAverageComplex_succ_on_Ici hh.le (hF 0) hx]
    have hi : (∫ u in (0 : ℝ)..h, iteratedBoxAverageComplex h n (F 0) (x + u)) =
        ((h : ℂ) ^ n)⁻¹ * ∫ u in (0 : ℝ)..h, ((fwdDiff h)^[n] (F n)) (x + u) := by
      rw [← integral_const_mul]
      apply integral_congr
      intro u hu
      rw [uIcc_of_le hh.le] at hu
      exact ih (by linarith [hu.1])
    rw [hi, integral_comp_add_left]
    simp only [add_zero]
    have hsub : uIcc x (x + h) ⊆ Ici a := by
      rw [uIcc_of_le (by linarith : x ≤ x + h)]
      exact fun _ ht => hx.trans ht.1
    have hp := integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_fwdDiff_iter_Ici hh.le (hderiv n) n (hsub ht))
      ((continuousOn_fwdDiff_iter_Ici hh.le (hF n) n).mono hsub).intervalIntegrable
    rw [hp, iterate_succ_apply']
    simp only [fwdDiff, pow_succ, mul_inv, ofReal_inv]
    ring

end

end intervalIntegral
