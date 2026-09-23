import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageStability

/-! # Support-local error propagation, including zero order and zero step -/

open Complex Set intervalIntegral

example {h a x C : ℝ} (hh : 0 < h) {f g : ℝ → ℂ}
    (hf : ContinuousOn f (Ici a)) (hg : ContinuousOn g (Ici a)) (hax : a ≤ x) (n : ℕ)
    (hb : ∀ t ∈ Icc x (x + n * h), ‖f t - g t‖ ≤ C) :
    ‖iteratedBoxAverageComplex h n f x - iteratedBoxAverageComplex h n g x‖ ≤ C :=
  norm_iteratedBoxAverageComplex_sub_le_on_Ici hh hf hg hax n hb

example {a x : ℝ} {f g : ℝ → ℂ} (hf : ContinuousOn f (Ici a))
    (hg : ContinuousOn g (Ici a)) (hax : a ≤ x) (n : ℕ) :
    iteratedBoxAverageComplex 0 n (fun t => f t - g t) x =
      iteratedBoxAverageComplex 0 n f x - iteratedBoxAverageComplex 0 n g x :=
  iteratedBoxAverageComplex_sub_on_Ici le_rfl hf hg hax n

example {h x C : ℝ} (hh : 0 < h) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hb : ‖f x - g x‖ ≤ C) :
    ‖iteratedBoxAverageComplex h 0 f x - iteratedBoxAverageComplex h 0 g x‖ ≤ C := by
  apply norm_iteratedBoxAverageComplex_sub_le_on_Ici hh hf.continuousOn hg.continuousOn le_rfl
  simpa only [Nat.cast_zero, zero_mul, add_zero, Icc_self, mem_singleton_iff, forall_eq] using hb
