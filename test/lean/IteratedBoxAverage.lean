import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageAlgebra
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageRegularity
import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageSupport

/-! # Algebra and regularity regressions for arbitrary-order averages -/

open intervalIntegral

example {h : ℝ} (hh : 0 < h) {f : ℝ → ℝ} (hf : Monotone f) (m : ℕ) :
    ContDiff ℝ m (iteratedBoxAverage h (m + 1) f) :=
  contDiff_iteratedBoxAverage_succ hh hf m

example {h : ℝ} (hh : 0 < h) {f : ℝ → ℝ} (hf : Monotone f) :
    Continuous (iteratedBoxAverage h 1 f) := continuous_iteratedBoxAverage_succ hh hf 0

example {h : ℝ} (hh : 0 < h) {f : ℝ → ℝ} (hf : Monotone f) :
    ContDiff ℝ 2 (iteratedBoxAverage h 3 f) := contDiff_iteratedBoxAverage_succ hh hf 2

example {h : ℝ} {m : ℕ} {f : ℝ → ℝ} (hc : Continuous (iteratedBoxAverage h m f)) (x : ℝ) :
    HasDerivAt (iteratedBoxAverage h (m + 1) f)
      (h⁻¹ * (iteratedBoxAverage h m f (x + h) - iteratedBoxAverage h m f x)) x :=
  hasDerivAt_iteratedBoxAverage_succ hc x

example (h : ℝ) (m : ℕ) (f : ℝ → ℝ) (c x : ℝ) :
    iteratedBoxAverage h m (fun t => f (t + c)) x = iteratedBoxAverage h m f (x + c) :=
  iteratedBoxAverage_translate h m f c x

example {h : ℝ} (hh : 0 ≤ h) (m : ℕ) {f g : ℝ → ℝ} {x : ℝ}
    (he : Set.EqOn f g (Set.Icc x (x + m * h))) :
    iteratedBoxAverage h m f x = iteratedBoxAverage h m g x :=
  iteratedBoxAverage_congr_on hh m he

example (h : ℝ) (m : ℕ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedBoxAverage h m (fun t => c * f t) x = c * iteratedBoxAverage h m f x :=
  iteratedBoxAverage_const_mul h m c f x

example {ι : Type*} {h : ℝ} (hh : 0 < h) (m : ℕ) (S : Finset ι)
    (f : ι → ℝ → ℝ) (hf : ∀ i ∈ S, Monotone (f i)) (x : ℝ) :
    iteratedBoxAverage h m (fun t => ∑ i ∈ S, f i t) x =
      ∑ i ∈ S, iteratedBoxAverage h m (f i) x := iteratedBoxAverage_sum hh m S f hf x
