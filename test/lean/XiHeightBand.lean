import PrimeFactorUnimodality.Helpers.Analytic.XiHeightBandGap

/-! # Boundary, multiplicity, and initial-region regressions for the xi band -/

namespace PrimeFactorUnimodality.Tests

noncomputable section

local instance : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _

example (H : ℝ) : xiHeightBandIndices H H = ∅ := xiHeightBandIndices_self H

example {H T : ℝ} {p : RiemannXiDivisorZeroIndex}
    (hp : |(riemannXiDivisorZeroValue p).im| = H) (hHT : H < T) :
    p ∈ xiHeightBandIndices H T := by
  rw [mem_xiHeightBandIndices, hp]
  exact ⟨le_rfl, hHT⟩

example {H T : ℝ} {p : RiemannXiDivisorZeroIndex}
    (hp : |(riemannXiDivisorZeroValue p).im| = T) :
    p ∉ xiHeightBandIndices H T := by simp [mem_xiHeightBandIndices, hp]

example {H T : ℝ} (hHT : H ≤ T) :
    xiLowHeightIndices H ∪ xiHeightBandIndices H T = xiLowHeightIndices T :=
  xiLowHeightIndices_union_band hHT

example (H T : ℝ) : Disjoint (xiLowHeightIndices H) (xiHeightBandIndices H T) :=
  disjoint_xiLowHeightIndices_band H T

example {H T : ℝ} (hH : 0 < H) :
    (∑ p ∈ xiHeightBandIndices H T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      2 * ∑ p ∈ xiHeightWindowIndices (H / 2) T,
        ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖ :=
  sum_xi_band_reciprocal_norm_le_twice_window hH

example {H T : ℝ} (hH : 20 ≤ H) (hHT : H ≤ T) :
    (∑ p ∈ xiHeightBandIndices H T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      xiBandReciprocalNormBound H T := sum_xi_band_reciprocal_norm_le_bound hH hHT

example (H : ℝ) : xiBandReciprocalNormBound H H = 0 := by simp

example {T : ℝ} (hT : 10 ^ 9 ≤ T) : 0 < 1 / (56 * Real.log T) := xi_initial_gap_pos hT

example {H T : ℝ} (hH : 10 ^ 9 ≤ H) {p : RiemannXiDivisorZeroIndex}
    (hp : p ∈ xiHeightBandIndices H T) :
    (riemannXiDivisorZeroValue p).re ≤ 1 - 1 / (56 * Real.log T) :=
  xi_height_band_re_le_initial_gap hH hp

end

end PrimeFactorUnimodality.Tests
