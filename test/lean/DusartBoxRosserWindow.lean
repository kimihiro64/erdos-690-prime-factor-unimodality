import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserWindow

/-! # Actual box atoms and finite sums retain full damped-height decay -/

namespace PrimeFactorUnimodality.Tests

open intervalIntegral

example (m : ℕ) {h x R : ℝ} (hh : 0 < h) (hx : 1 < x) (hR : 0 < R)
    {s : ℂ} (hγ : 1 < s.im) (hβ0 : 0 ≤ s.re)
    (hβ : s.re ≤ 1 - 1 / (R * Real.log s.im)) :
    ‖iteratedBoxAverageComplex h (m + 3) (fun t => (t : ℂ) ^ s / s) x‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        Real.logDampedPower (Real.log x / R) (m + 4 : ℕ) s.im :=
  norm_dusartBox_atom_le_rosser_kernel m hh hx hR hγ hβ0 hβ

example (m : ℕ) {h x R u v : ℝ} (hh : 0 < h) (hx : 1 < x) (hR : 0 < R)
    (hu : 10 ≤ u) (huv : u ≤ v)
    (hreg : ∀ p ∈ xiHeightWindowIndices u v,
      (riemannXiDivisorZeroValue p).re ≤
        1 - 1 / (R * Real.log (riemannXiDivisorZeroValue p).im)) :
    ‖∑ p ∈ xiHeightWindowIndices u v, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        xiRosserWindowBound (Real.log x / R) (m + 4 : ℕ) u v :=
  norm_dusartBox_xi_window_le_rosser m hh hx hR hu huv hreg

example (m : ℕ) {h x u v : ℝ} (hh : 0 < h) (hx : 1 < x)
    (hu : 10 ^ 9 ≤ u) (huv : u ≤ v) :
    ‖∑ p ∈ xiHeightWindowIndices u v, iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        xiRosserWindowBound (Real.log x / 56) (m + 4 : ℕ) u v :=
  norm_dusartBox_xi_window_le_initial_rosser m hh hx hu huv

example (m : ℕ) (h x u : ℝ) :
    (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
      xiRosserWindowBound (Real.log x / 56) (m + 4 : ℕ) u u = 0 := by simp

end PrimeFactorUnimodality.Tests
