/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverage

/-! # Finite linear combinations of iterated averages

Scalar multiplication commutes with every average. For a finite family
of monotone functions, all intermediate integrability requirements are
automatic, so the average also commutes with the finite sum.
-/

open MeasureTheory

namespace intervalIntegral

noncomputable section

theorem iteratedBoxAverage_const_mul (h : ℝ) (m : ℕ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedBoxAverage h m (fun t => c * f t) x = c * iteratedBoxAverage h m f x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    change h⁻¹ * (∫ u in (0 : ℝ)..h,
      iteratedBoxAverage h m (fun t => c * f t) (x + u)) =
      c * (h⁻¹ * ∫ u in (0 : ℝ)..h, iteratedBoxAverage h m f (x + u))
    simp_rw [ih]
    rw [integral_const_mul]
    ring

theorem iteratedBoxAverage_sum {ι : Type*} {h : ℝ} (hh : 0 < h)
    (m : ℕ) (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ S, Monotone (f i)) (x : ℝ) :
    iteratedBoxAverage h m (fun t => ∑ i ∈ S, f i t) x =
      ∑ i ∈ S, iteratedBoxAverage h m (f i) x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    change h⁻¹ * (∫ u in (0 : ℝ)..h,
      iteratedBoxAverage h m (fun t => ∑ i ∈ S, f i t) (x + u)) =
      ∑ i ∈ S, h⁻¹ * ∫ u in (0 : ℝ)..h, iteratedBoxAverage h m (f i) (x + u)
    simp_rw [ih]
    rw [integral_finsetSum]
    · exact Finset.mul_sum ..
    · intro i hi
      exact ((monotone_iteratedBoxAverage hh (hf i hi) m).comp
        (monotone_const.add monotone_id)).intervalIntegrable

end

end intervalIntegral
