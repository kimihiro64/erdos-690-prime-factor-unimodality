/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverage

/-! # Regularity gained by successive interval averages

The first average of a monotone function is continuous, even when the
function has jumps. Each further average gains a continuous derivative.
The proof uses Mathlib's continuous primitive and fundamental theorem of
calculus; no distributional or differentiation-under-integral hypothesis
is needed.
-/

open MeasureTheory

namespace intervalIntegral

noncomputable section

/-- A sliding average is the difference of two values of a fixed primitive. -/
theorem iteratedBoxAverage_succ_eq_sub_primitive {h : ℝ} {m : ℕ} {f : ℝ → ℝ}
    (hint : ∀ a b, IntervalIntegrable (iteratedBoxAverage h m f) volume a b) (x : ℝ) :
    iteratedBoxAverage h (m + 1) f x = h⁻¹ *
      ((∫ t in (0 : ℝ)..x + h, iteratedBoxAverage h m f t) -
        ∫ t in (0 : ℝ)..x, iteratedBoxAverage h m f t) := by
  rw [iteratedBoxAverage, integral_comp_add_left]
  simp only [add_zero]
  rw [integral_interval_sub_left (hint _ _) (hint _ _)]

/-- One positive-width average of a monotone function is continuous everywhere. -/
theorem continuous_iteratedBoxAverage_succ {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℝ} (hf : Monotone f) (m : ℕ) :
    Continuous (iteratedBoxAverage h (m + 1) f) := by
  have hint : ∀ a b, IntervalIntegrable (iteratedBoxAverage h m f) volume a b :=
    fun _ _ => (monotone_iteratedBoxAverage hh hf m).intervalIntegrable
  have hp := continuous_primitive hint 0
  have he : iteratedBoxAverage h (m + 1) f = fun x => h⁻¹ *
      ((∫ t in (0 : ℝ)..x + h, iteratedBoxAverage h m f t) -
        ∫ t in (0 : ℝ)..x, iteratedBoxAverage h m f t) :=
    funext (iteratedBoxAverage_succ_eq_sub_primitive hint)
  rw [he]
  exact ((hp.comp (continuous_id.add_const h)).sub hp).const_mul _

/-- Once the preceding average is continuous, its endpoint difference is the derivative. -/
theorem hasDerivAt_iteratedBoxAverage_succ {h : ℝ} {m : ℕ} {f : ℝ → ℝ}
    (hc : Continuous (iteratedBoxAverage h m f)) (x : ℝ) :
    HasDerivAt (iteratedBoxAverage h (m + 1) f)
      (h⁻¹ * (iteratedBoxAverage h m f (x + h) - iteratedBoxAverage h m f x)) x := by
  have hp := (hc.integral_hasStrictDerivAt 0 (x + h)).hasDerivAt.comp x
    ((hasDerivAt_id x).add_const h)
  have hq := (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hd := (hp.sub hq).const_mul h⁻¹
  have he : iteratedBoxAverage h (m + 1) f = fun x => h⁻¹ *
      ((∫ t in (0 : ℝ)..x + h, iteratedBoxAverage h m f t) -
        ∫ t in (0 : ℝ)..x, iteratedBoxAverage h m f t) :=
    funext (iteratedBoxAverage_succ_eq_sub_primitive (fun _ _ => hc.intervalIntegrable _ _))
  rw [he]
  simpa only [Function.comp_def, id_eq, Pi.sub_apply, mul_one] using hd

/-- After `m+1` positive-width averages, every monotone function is `C^m`. -/
theorem contDiff_iteratedBoxAverage_succ {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℝ} (hf : Monotone f) (m : ℕ) :
    ContDiff ℝ m (iteratedBoxAverage h (m + 1) f) := by
  induction m with
  | zero => exact contDiff_zero.mpr (continuous_iteratedBoxAverage_succ hh hf 0)
  | succ m ih =>
    have hd := hasDerivAt_iteratedBoxAverage_succ ih.continuous
    have he : deriv (iteratedBoxAverage h (m + 1 + 1) f) = fun x =>
        h⁻¹ * (iteratedBoxAverage h (m + 1) f (x + h) -
          iteratedBoxAverage h (m + 1) f x) := funext (fun x => (hd x).deriv)
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hd x).differentiableAt, by simp, ?_⟩
    rw [he]
    exact contDiff_const.mul ((ih.comp (contDiff_id.add contDiff_const)).sub ih)

end

end intervalIntegral
