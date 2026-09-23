/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageAlgebra
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageComplex

/-! # Conjugation of complex box averages

Conjugation commutes with every averaging order, even without integrability
hypotheses. On positive support it also commutes with divided complex powers.
-/

namespace intervalIntegral

noncomputable section

open Complex
open scoped ComplexConjugate

/-- Conjugation is compatible with componentwise averaging for every step and order. -/
theorem iteratedBoxAverageComplex_conj (h : ℝ) (n : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    iteratedBoxAverageComplex h n (fun t => conj (f t)) x =
      conj (iteratedBoxAverageComplex h n f x) := by
  apply Complex.ext
  · rfl
  · change iteratedBoxAverage h n (fun t => -(f t).im) x =
      -iteratedBoxAverage h n (fun t => (f t).im) x
    simpa only [neg_one_mul] using iteratedBoxAverage_const_mul h n (-1)
      (fun t => (f t).im) x

/-- Positive support avoids the branch cut when conjugating the divided power. -/
theorem iteratedBoxAverageComplex_cpow_div_conj {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) (n : ℕ) (z : ℂ) :
    iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ conj z / conj z) x =
      conj (iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ z / z) x) := by
  rw [← iteratedBoxAverageComplex_conj]
  apply iteratedBoxAverageComplex_congr_on hh n
  intro t ht
  have htpos : 0 < t := hx.trans_le ht.1
  change (t : ℂ) ^ conj z / conj z = conj ((t : ℂ) ^ z / z)
  rw [map_div₀, cpow_conj _ _ (by rw [arg_ofReal_of_nonneg htpos.le]; exact Real.pi_ne_zero.symm)]
  simp

end

end intervalIntegral
