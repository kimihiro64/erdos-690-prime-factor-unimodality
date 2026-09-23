import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAveragePower

/-! # Regression checks for the arbitrary-order power average

Exercise zero order, zero-step support estimates, local continuity,
the exact one-step denominator, positive real and nonreal exponents,
and every natural order in the quantitative bound.
-/

open Complex Function Set intervalIntegral

example {x C : ℝ} (n : ℕ) {f : ℝ → ℂ} (hf : ‖f x‖ ≤ C) :
    ‖((fwdDiff 0)^[n] f) x‖ ≤ 2 ^ n * C := by
  apply norm_fwdDiff_iter_le (by norm_num)
  intro t ht
  have he : t = x := by
    have ht' : x ≤ t ∧ t ≤ x := by simpa only [mul_zero, add_zero, mem_Icc] using ht
    exact le_antisymm ht'.2 ht'.1
  simpa only [he] using hf

example {a h x : ℝ} (hh : 0 ≤ h) {f g : ℝ → ℂ}
    (hf : ∀ t ∈ Ici a, HasDerivAt f (g t) t) (n : ℕ) (hx : a ≤ x) :
    HasDerivAt ((fwdDiff h)^[n] f) (((fwdDiff h)^[n] g) x) x :=
  hasDerivAt_fwdDiff_iter_Ici hh hf n hx

example {a h x : ℝ} (hh : 0 ≤ h) {f : ℝ → ℂ} (hf : ContinuousOn f (Ici a))
    (hx : a ≤ x) (n : ℕ) :
    iteratedBoxAverageComplex h (n + 1) f x =
      (h⁻¹ : ℝ) * ∫ u in (0 : ℝ)..h, iteratedBoxAverageComplex h n f (x + u) :=
  iteratedBoxAverageComplex_succ_on_Ici hh hf hx n

example (s : ℂ) (t : ℝ) : cpowPrimitive s 0 t = (t : ℂ) ^ s / s := cpowPrimitive_zero s t

example {s : ℂ} (hs : s.im ≠ 0) (n : ℕ) : cpowPrimitiveDenom s n ≠ 0 :=
  cpowPrimitiveDenom_ne_zero (add_natCast_ne_zero_of_im_ne_zero hs) n

example (s : ℂ) (n : ℕ) : |s.im| ^ (n + 1) ≤ ‖cpowPrimitiveDenom s n‖ :=
  pow_abs_im_le_norm_cpowPrimitiveDenom s n

example {s : ℂ} (hs : ∀ j : ℕ, s + j ≠ 0) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (cpowPrimitive s (n + 1)) (cpowPrimitive s n t) t :=
  hasDerivAt_cpowPrimitive_succ hs n ht

example {h x : ℝ} (hh : 0 < h) (hx : 0 < x) {s : ℂ} (hs : ∀ j : ℕ, s + j ≠ 0) :
    iteratedBoxAverageComplex h 1 (fun t => (t : ℂ) ^ s / s) x =
      (((x + h : ℝ) : ℂ) ^ (s + 1) - (x : ℂ) ^ (s + 1)) /
        ((h : ℂ) * (s * (s + 1))) := by
  simpa only [Function.iterate_one, fwdDiff, Nat.cast_one, pow_one,
    cpowPrimitiveDenom_succ, cpowPrimitiveDenom_zero, Nat.cast_zero, zero_add] using
      iteratedBoxAverageComplex_cpow_div_eq_difference hh hx hs 1

example {h x : ℝ} (hh : 0 < h) (hx : 0 < x) {s : ℂ}
    (hs : ∀ j : ℕ, s + j ≠ 0) (hβ : 0 ≤ s.re) (n : ℕ) :
    ‖iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ s / s) x‖ ≤
      2 ^ n * (x + n * h) ^ (s.re + n) / (h ^ n * ‖cpowPrimitiveDenom s n‖) :=
  norm_iteratedBoxAverageComplex_cpow_div_le hh hx hs hβ n

example {h x : ℝ} (hh : 0 < h) (hx : 0 < x) {s : ℂ}
    (hs : s.im ≠ 0) (hβ : 0 ≤ s.re) (n : ℕ) :
    ‖iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ s / s) x‖ ≤
      2 ^ n * (x + n * h) ^ (s.re + n) / (h ^ n * |s.im| ^ (n + 1)) :=
  norm_iteratedBoxAverageComplex_cpow_div_le_height hh hx hs hβ n
