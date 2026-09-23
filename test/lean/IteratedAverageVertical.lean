import PrimeFactorUnimodality.Mathlib.MeasureTheory.Integral.IntervalIntegral.IteratedAverageVertical

/-! # Arbitrary vertical lines and orders use a lower norm, not a zero-location assumption -/

open Complex intervalIntegral

example {x L : ℝ} (hx : 0 < x) {z w : ℂ} (he : z.re = w.re)
    (hL : 0 < L) (hz : L ≤ ‖z‖) (hw : L ≤ ‖w‖) :
    ‖(x : ℂ) ^ z / z - (x : ℂ) ^ w / w‖ ≤
      Real.exp (z.re * Real.log x) *
        (‖z - w‖ / L ^ 2 + |Real.log x| * |z.im - w.im| / L) :=
  norm_cpow_div_sub_le_of_re_eq hx he hL hz hw

example {h L : ℝ} (hh : 0 < h) {z w : ℂ} (he : z.re = w.re) (hβ : 0 ≤ z.re)
    (hL : 0 < L) (hz : L ≤ ‖z‖) (hw : L ≤ ‖w‖) (n : ℕ) :
    ‖iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ z / z) 1 -
      iteratedBoxAverageComplex h n (fun t => (t : ℂ) ^ w / w) 1‖ ≤
      Real.exp (z.re * Real.log (1 + n * h)) *
        (‖z - w‖ / L ^ 2 + Real.log (1 + n * h) * |z.im - w.im| / L) :=
  norm_iteratedBoxAverageComplex_cpow_div_sub_le hh he hβ hL hz hw n

example {h L : ℝ} (hh : 0 < h) {z : ℂ} (hβ : 0 ≤ z.re) (hL : 0 < L) (hz : L ≤ ‖z‖) :
    ‖iteratedBoxAverageComplex h 0 (fun t => (t : ℂ) ^ z / z) 1‖ ≤ 1 / L := by
  simpa using norm_iteratedBoxAverageComplex_cpow_div_le_of_norm_ge hh hβ hL hz 0
