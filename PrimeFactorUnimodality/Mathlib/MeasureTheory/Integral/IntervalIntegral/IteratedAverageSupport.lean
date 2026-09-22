/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverage

/-! # Translations and local dependence of iterated interval averages

Only the values on the finite averaging support affect the result.
In particular, a constant plateau is preserved whenever the complete
support lies inside it. The translation identity has no regularity premise.
-/

namespace intervalIntegral

noncomputable section

/-- Translating a function translates each of its iterated averages. -/
theorem iteratedBoxAverage_translate (h : ℝ) (m : ℕ) (f : ℝ → ℝ) (c x : ℝ) :
    iteratedBoxAverage h m (fun t => f (t + c)) x = iteratedBoxAverage h m f (x + c) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    change h⁻¹ * (∫ u in (0 : ℝ)..h,
      iteratedBoxAverage h m (fun t => f (t + c)) (x + u)) =
      h⁻¹ * ∫ u in (0 : ℝ)..h, iteratedBoxAverage h m f (x + c + u)
    congr 1
    apply integral_congr
    intro u _
    dsimp only
    rw [ih]
    exact congrArg (iteratedBoxAverage h m f) (by ring)

/-- An iterated average depends only on the function's values on its support. -/
theorem iteratedBoxAverage_congr_on {h : ℝ} (hh : 0 ≤ h) (m : ℕ)
    {f g : ℝ → ℝ} {x : ℝ} (he : Set.EqOn f g (Set.Icc x (x + m * h))) :
    iteratedBoxAverage h m f x = iteratedBoxAverage h m g x := by
  induction m generalizing x with
  | zero => exact he (by simp)
  | succ m ih =>
    simp only [iteratedBoxAverage]
    congr 1
    apply integral_congr
    intro u hu
    rw [Set.uIcc_of_le hh] at hu
    apply ih
    intro t ht
    apply he
    constructor
    · linarith [hu.1, ht.1]
    · push_cast
      linarith [hu.2, ht.2]

/-- A plateau is unchanged if it contains the entire averaging support. -/
theorem iteratedBoxAverage_eq_const {h : ℝ} (hh : 0 < h) (m : ℕ)
    {f : ℝ → ℝ} {c x : ℝ} (he : ∀ t ∈ Set.Icc x (x + m * h), f t = c) :
    iteratedBoxAverage h m f x = c :=
  (iteratedBoxAverage_congr_on hh.le m he).trans (iteratedBoxAverage_const hh.ne' m c x)

end

end intervalIntegral
