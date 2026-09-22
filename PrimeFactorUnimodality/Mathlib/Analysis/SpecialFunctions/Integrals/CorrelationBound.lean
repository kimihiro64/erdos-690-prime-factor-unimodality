/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

/-! # A finite-interval correlation bound

The absolute correlation over two overlapping translates of an interval
is bounded by the square integral over the full interval. The proof uses
the pointwise inequality `2*|x*y| <= x^2+y^2` and translation of integrals.
-/

namespace intervalIntegral

open MeasureTheory

/-- A translated overlap correlation is bounded by the original square integral. -/
theorem abs_integral_mul_translate_le_integral_sq {f : ℝ → ℝ} (hf : Continuous f)
    {a b u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ b - a) :
    |∫ v in a..b - u, f v * f (v + u)| ≤ ∫ v in a..b, f v ^ 2 := by
  have hab : a ≤ b - u := by linarith
  have hshift : Continuous (fun v => f (v + u)) := hf.comp (continuous_id.add continuous_const)
  have hs := (hf.pow 2).intervalIntegrable (μ := volume) (a := a) (b := b - u)
  have ht := (hshift.pow 2).intervalIntegrable (μ := volume) (a := a) (b := b - u)
  have hfull := (hf.pow 2).intervalIntegrable (μ := volume) (a := a) (b := b)
  have hleft := integral_mono_interval (le_refl a) hab (by linarith : b - u ≤ b)
    (Filter.Eventually.of_forall fun v => sq_nonneg (f v)) hfull
  have hright := integral_mono_interval (by linarith : a ≤ a + u)
    (by linarith : a + u ≤ b) (le_refl b)
    (Filter.Eventually.of_forall fun v => sq_nonneg (f v)) hfull
  have htranslate : (∫ v in a..b - u, f (v + u) ^ 2) = ∫ v in a + u..b, f v ^ 2 := by
    rw [integral_comp_add_right (fun v => f v ^ 2) u]
    simp
  have hbound : (∫ v in a..b - u, |f v * f (v + u)|) ≤
      ∫ v in a..b - u, (f v ^ 2 + f (v + u) ^ 2) / 2 := by
    apply integral_mono hab ((hf.mul hshift).abs.intervalIntegrable a (b - u))
      ((hs.add ht).div_const 2)
    intro v
    dsimp
    rw [abs_mul]
    nlinarith [sq_nonneg (|f v| - |f (v + u)|), sq_abs (f v), sq_abs (f (v + u))]
  rw [integral_div, integral_add
    (f := fun v => f v ^ 2) (g := fun v => f (v + u) ^ 2) hs ht, htranslate] at hbound
  have hnorm := abs_integral_le_integral_abs (μ := volume) (f := fun v => f v * f (v + u)) hab
  linarith

end intervalIntegral
