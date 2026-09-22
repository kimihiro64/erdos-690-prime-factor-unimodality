/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageRegularity

/-! # Continuous inputs and affine terms in interval averages

Continuous inputs remain continuous at every averaging order. This gives
the integrability needed to subtract constants even for nonmonotone inputs.
-/

open MeasureTheory

namespace intervalIntegral

noncomputable section

theorem continuous_iteratedBoxAverage (h : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    Continuous (iteratedBoxAverage h n f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    have hint : ∀ a b, IntervalIntegrable (iteratedBoxAverage h n f) volume a b :=
      fun a b => ih.intervalIntegrable a b
    have hp := continuous_primitive hint 0
    have he := funext (iteratedBoxAverage_succ_eq_sub_primitive hint)
    rw [he]
    exact ((hp.comp (continuous_id.add_const h)).sub hp).const_mul _

theorem iteratedBoxAverage_sub_const {h : ℝ} (hh : h ≠ 0)
    {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) (c x : ℝ) :
    iteratedBoxAverage h n (fun t => f t - c) x = iteratedBoxAverage h n f x - c := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hi : IntervalIntegrable (fun u => iteratedBoxAverage h n f (x + u)) volume 0 h :=
      ((continuous_iteratedBoxAverage h hf n).comp
      (continuous_const.add continuous_id)).intervalIntegrable 0 h
    simp only [iteratedBoxAverage, ih]
    rw [integral_sub hi intervalIntegrable_const, integral_const]
    simp only [sub_zero, smul_eq_mul]
    field_simp [hh]

theorem iteratedBoxAverage_id {h : ℝ} (hh : 0 < h) (n : ℕ) (x : ℝ) :
    iteratedBoxAverage h n id x = x + n * h / 2 := by
  have he := iteratedBoxAverage_sub_id hh monotone_id n x
  have hz : (fun t : ℝ => id t - t) = (fun _ => 0) := by funext t; simp
  rw [hz, iteratedBoxAverage_const hh.ne'] at he
  linarith

end

end intervalIntegral
