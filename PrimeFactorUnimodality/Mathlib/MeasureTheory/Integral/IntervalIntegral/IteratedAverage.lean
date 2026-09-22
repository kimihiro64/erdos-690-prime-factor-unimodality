/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Iterated interval averages of monotone functions

An average over `m` positive intervals lies between the values at the
two ends of its support. Subtracting the identity function gives the
exact centering correction `m * h / 2`. No continuity of the monotone
function is required, so this applies to discontinuous counting functions.
-/

open MeasureTheory

namespace intervalIntegral

noncomputable section

/-- Average over `m` successive translates by a uniform interval of length `h`. -/
def iteratedBoxAverage (h : ℝ) : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f, x => f x
  | m + 1, f, x => h⁻¹ * ∫ u in (0 : ℝ)..h, iteratedBoxAverage h m f (x + u)

/-- Every nondegenerate iterated average preserves constants exactly. -/
theorem iteratedBoxAverage_const {h : ℝ} (hh : h ≠ 0) (m : ℕ) (c x : ℝ) :
    iteratedBoxAverage h m (fun _ => c) x = c := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => simp [iteratedBoxAverage, ih, hh]

/-- Averaging preserves monotonicity, including for discontinuous functions. -/
theorem monotone_iteratedBoxAverage {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℝ} (hf : Monotone f) (m : ℕ) : Monotone (iteratedBoxAverage h m f) := by
  induction m with
  | zero => exact hf
  | succ m ih =>
    intro x y hxy
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hh.le)
    exact integral_mono_on hh.le
      ((ih.comp (monotone_const.add monotone_id)).intervalIntegrable)
      ((ih.comp (monotone_const.add monotone_id)).intervalIntegrable)
      (fun u _ => ih (by linarith))

/-- Every iterated average is enclosed by the two endpoint values of its support. -/
theorem iteratedBoxAverage_mem_Icc {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℝ} (hf : Monotone f) (m : ℕ) (x : ℝ) :
    iteratedBoxAverage h m f x ∈ Set.Icc (f x) (f (x + m * h)) := by
  induction m generalizing x with
  | zero => simp [iteratedBoxAverage]
  | succ m ih =>
    have hint : IntervalIntegrable (fun u => iteratedBoxAverage h m f (x + u))
        volume 0 h :=
      ((monotone_iteratedBoxAverage hh hf m).comp
        (monotone_const.add monotone_id)).intervalIntegrable
    constructor
    · calc
        f x = h⁻¹ * ∫ _ in (0 : ℝ)..h, f x := by simp [hh.ne']
        _ ≤ iteratedBoxAverage h (m + 1) f x := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hh.le)
          exact integral_mono_on hh.le intervalIntegrable_const hint
            (fun u hu => (hf (by linarith [hu.1])).trans (ih (x + u)).1)
    · calc
        iteratedBoxAverage h (m + 1) f x ≤
            h⁻¹ * ∫ _ in (0 : ℝ)..h, f (x + (m + 1 : ℕ) * h) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hh.le)
          apply integral_mono_on hh.le hint intervalIntegrable_const
          intro u hu
          exact (ih (x + u)).2.trans (hf (by push_cast; linarith [hu.2]))
        _ = f (x + (m + 1 : ℕ) * h) := by simp [hh.ne']

/-- Subtracting the main term commutes with averaging, with its exact mean shift. -/
theorem iteratedBoxAverage_sub_id {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℝ} (hf : Monotone f) (m : ℕ) (x : ℝ) :
    iteratedBoxAverage h m (fun t => f t - t) x =
      iteratedBoxAverage h m f x - x - m * h / 2 := by
  induction m generalizing x with
  | zero => simp [iteratedBoxAverage]
  | succ m ih =>
    have hint : IntervalIntegrable (fun u => iteratedBoxAverage h m f (x + u))
        volume 0 h :=
      ((monotone_iteratedBoxAverage hh hf m).comp
        (monotone_const.add monotone_id)).intervalIntegrable
    have hid : IntervalIntegrable (fun u : ℝ => x + u) volume 0 h :=
      (continuous_const.add continuous_id).intervalIntegrable _ _
    simp only [iteratedBoxAverage, ih]
    rw [integral_sub (hint.sub hid) intervalIntegrable_const, integral_sub hint hid,
      integral_add (f := fun _ : ℝ => x) (g := fun u : ℝ => u)
        intervalIntegrable_const (continuous_id.intervalIntegrable 0 h),
      integral_const, integral_id, integral_const]
    simp only [sub_zero, zero_pow (by decide : 2 ≠ 0), smul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hh.ne']
    ring

/-- The two adjacent average errors enclose the pointwise error with half-width loss. -/
theorem sub_id_bounds_of_iteratedBoxAverage {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℝ} (hf : Monotone f) (m : ℕ) (x : ℝ) :
    iteratedBoxAverage h m (fun t => f t - t) (x - m * h) - m * h / 2 ≤ f x - x ∧
      f x - x ≤ iteratedBoxAverage h m (fun t => f t - t) x + m * h / 2 := by
  have hlo := (iteratedBoxAverage_mem_Icc hh hf m (x - m * h)).2
  have hhi := (iteratedBoxAverage_mem_Icc hh hf m x).1
  rw [sub_add_cancel] at hlo
  rw [iteratedBoxAverage_sub_id hh hf, iteratedBoxAverage_sub_id hh hf]
  constructor <;> linarith

end

end intervalIntegral
