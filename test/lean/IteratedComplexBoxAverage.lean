import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Pow.ComplexDecay
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageComplex

/-! # Regression checks for continuous and complex interval averages

Include zero order, zero width for continuity, nonmonotone continuous
inputs, local half-line assumptions, and the zero complex exponent in
the totalized BV bound.
-/

open Complex Set intervalIntegral

example (h : ℝ) (f : ℝ → ℂ) (x : ℝ) : iteratedBoxAverageComplex h 0 f x = f x := rfl

example {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    Continuous (iteratedBoxAverage 0 n f) := continuous_iteratedBoxAverage 0 hf n

example {h : ℝ} (hh : 0 < h) (n : ℕ) (x : ℝ) :
    iteratedBoxAverage h n id x = x + n * h / 2 := iteratedBoxAverage_id hh n x

example {h : ℝ} (hh : h ≠ 0) (n : ℕ) (c x : ℝ) :
    iteratedBoxAverage h n (fun t => Real.sin t - c) x =
      iteratedBoxAverage h n Real.sin x - c :=
  iteratedBoxAverage_sub_const hh Real.continuous_sin n c x

example (h : ℝ) {f : ℝ → ℂ} (hf : Continuous f) (n : ℕ) (x : ℝ) :
    iteratedBoxAverageComplex h (n + 1) f x =
      (h⁻¹ : ℝ) * ∫ u in (0 : ℝ)..h, iteratedBoxAverageComplex h n f (x + u) :=
  iteratedBoxAverageComplex_succ h hf n x

example {h a x : ℝ} (hh : 0 < h) {f : ℝ → ℂ} (hf : ContinuousOn f (Ici a))
    (hax : a ≤ x) (n : ℕ) :
    iteratedBoxAverageComplex h n (fun t => f t - I) x =
      iteratedBoxAverageComplex h n f x - I :=
  iteratedBoxAverageComplex_sub_const_on_Ici hh hf hax n I

example {h a x C : ℝ} (hh : 0 < h) {f : ℝ → ℂ} (hf : ContinuousOn f (Ici a))
    (hax : a ≤ x) (n : ℕ) (hb : ∀ t ∈ Icc x (x + n * h), ‖f t‖ ≤ C) :
    ‖iteratedBoxAverageComplex h n f x‖ ≤ C :=
  norm_iteratedBoxAverageComplex_le_on_Ici hh hf hax n hb

example {h x : ℝ} (hh : 0 ≤ h) (n : ℕ) {f g : ℝ → ℂ}
    (he : EqOn f g (Icc x (x + n * h))) :
    iteratedBoxAverageComplex h n f x = iteratedBoxAverageComplex h n g x :=
  iteratedBoxAverageComplex_congr_on hh n he

example {y : ℝ} (hy : 1 ≤ y) :
    ‖(y : ℂ) ^ (0 : ℂ) / 0‖ ≤ (y * Real.exp (-Real.log y)) * ‖(1 : ℂ) / 0‖ := by
  simpa only [neg_one_mul] using
    norm_real_cpow_div_le_exp_gap_mul_reciprocal (δ := 1) (s := 0) hy (by norm_num)

example {y δ : ℝ} (hy : 1 ≤ y) {s : ℂ} (hs : s.re ≤ 1 - δ) :
    ‖(y : ℂ) ^ s / s‖ ≤ (y * Real.exp (-δ * Real.log y)) * ‖(1 : ℂ) / s‖ :=
  norm_real_cpow_div_le_exp_gap_mul_reciprocal hy hs
