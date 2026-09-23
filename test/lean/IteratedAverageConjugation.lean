import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageConjugation

/-! # Conjugation for arbitrary order and zero step -/

open Complex intervalIntegral
open scoped ComplexConjugate

example (h : ℝ) (n : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    iteratedBoxAverageComplex h n (fun t => conj (f t)) x =
      conj (iteratedBoxAverageComplex h n f x) :=
  iteratedBoxAverageComplex_conj h n f x

example {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) (n : ℕ) (z : ℂ) :
    iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ conj z / conj z) x =
      conj (iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ z / z) x) :=
  iteratedBoxAverageComplex_cpow_div_conj hh hx n z

example {x : ℝ} (hx : 0 < x) (z : ℂ) :
    iteratedBoxAverageComplex 0 0 (fun t => (t : ℂ) ^ conj z / conj z) x =
      conj (iteratedBoxAverageComplex 0 0 (fun t => (t : ℂ) ^ z / z) x) :=
  iteratedBoxAverageComplex_cpow_div_conj le_rfl hx 0 z
