import PrimeFactorUnimodality.Helpers.Analytic.XiRosserIncreasingBand

/-! # Increasing windows, band endpoints and generic conjugation-invariant weights -/

namespace PrimeFactorUnimodality.Tests

open Complex Real

example (a u : ℝ) : xiRosserIncreasingBound a u u = 0 := by simp

example (a H : ℝ) : xiRosserIncreasingBandBound a H H = 0 := by simp

example {a u v : ℝ}
    (ha : 0 < a) (hu : 10 ≤ u) (huv : u ≤ v) (hv : v ≤ exp (sqrt a)) :
    (∑ p ∈ xiHeightWindowIndices u v, logDampedPower a 1 (riemannXiDivisorZeroValue p).im) ≤
      xiRosserIncreasingBound a u v :=
  sum_xi_logDampedPower_one_le_increasing ha hu huv hv

example {a u : ℝ} (ha : 0 < a) (hu : 10 ≤ u) (huv : u ≤ exp (sqrt a)) :
    (∑ p ∈ xiHeightWindowIndices u (exp (sqrt a)),
      logDampedPower a 1 (riemannXiDivisorZeroValue p).im) ≤
        xiRosserIncreasingBound a u (exp (sqrt a)) :=
  sum_xi_logDampedPower_one_le_increasing ha hu huv le_rfl

example {a H T : ℝ} (ha : 0 < a) (hH : 20 ≤ H) (hHT : H ≤ T)
    (hT : T ≤ exp (sqrt a)) :
    (∑ p ∈ xiHeightBandIndices H T, logDampedPower a 1 |(riemannXiDivisorZeroValue p).im|) ≤
      xiRosserIncreasingBandBound a H T :=
  sum_xi_band_logDampedPower_one_le_increasing ha hH hHT hT

example {H T : ℝ} (hH : 0 < H) {f : RiemannXiDivisorZeroIndex → ℝ}
    (hf : ∀ p, 0 ≤ f p) (hc : ∀ p, f (riemannXiDivisorConjugation p) = f p) :
    (∑ p ∈ xiHeightBandIndices H T, f p) ≤
      2 * ∑ p ∈ xiHeightWindowIndices (H / 2) T, f p :=
  sum_xi_band_le_twice_window hH hf hc

example {H T : ℝ} (hH : 0 < H) :
    (∑ _p ∈ xiHeightBandIndices H T, (1 : ℝ)) ≤
      2 * ∑ _p ∈ xiHeightWindowIndices (H / 2) T, (1 : ℝ) :=
  sum_xi_band_le_twice_window hH (fun _ => by norm_num) (fun _ => rfl)

-- The existing reciprocal-norm specialization remains available unchanged.
example {H T : ℝ} (hH : 0 < H) :
    (∑ p ∈ xiHeightBandIndices H T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      2 * ∑ p ∈ xiHeightWindowIndices (H / 2) T,
        ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖ :=
  sum_xi_band_reciprocal_norm_le_twice_window hH

example (a q H : ℝ) :
    (∑ p ∈ xiHeightBandIndices H H, logDampedPower a q |(riemannXiDivisorZeroValue p).im|) =
      xiRosserIncreasingBandBound a H H := by simp

end PrimeFactorUnimodality.Tests
