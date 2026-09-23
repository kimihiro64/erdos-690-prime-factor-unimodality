import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxLowSplit

/-! # Split-low estimates: full powers, cutoff boundaries and uniform actual psi -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Real intervalIntegral

example (m : ℕ) {h x U H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hU : 1 < U) (hδ : 0 ≤ δ)
    (hgap : ∀ z ∈ xiHeightBandIndices U H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ) :
    ‖∑ z ∈ xiHeightBandIndices U H, iteratedBoxAverageComplex h (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x‖ ≤
      ((2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        exp (-δ * Real.log x)) * xiRosserAbsoluteTail 0 (m + 4 : ℕ) U :=
  norm_dusartBox_band_le_gap_tail m hh hx hU hδ hgap

example (q U : ℝ) :
    xiRosserPowerBandBound q U U = 0 :=
  xiRosserPowerBandBound_self q U

example {q U H : ℝ} (hq : 2 ≤ q) (hU : 10 < U) :
    0 ≤ xiRosserPowerBandBound q U H :=
  xiRosserPowerBandBound_nonneg hq hU

example (m : ℕ) {h x U H δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hU : 10 < U) (hUH : U ≤ H) (hδ : 0 ≤ δ)
    (hgap : ∀ z ∈ xiHeightBandIndices U H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ) :
    ‖∑ z ∈ xiHeightBandIndices U H, iteratedBoxAverageComplex h (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x‖ ≤
      ((2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        exp (-δ * Real.log x)) * xiRosserPowerBandBound (m + 4 : ℕ) U H :=
  norm_dusartBox_band_le_gap_power m hh hx hU hUH hδ hgap

example (m : ℕ) (s x a H δ : ℝ) :
    dusartBoxSplitLowBound m s x a H H δ =
      ((1 + (m + 3 : ℕ) * s) * exp (-δ * Real.log x)) *
        xiLowReciprocalNormBound a H δ :=
  dusartBoxSplitLowBound_self m s x a H δ

example (m : ℕ) {s x x₀ a U H δ : ℝ}
    (hs : 0 < s) (hx₀ : 1 < x₀) (hx : x₀ ≤ x)
    (ha : 10 ≤ a) (haU : a < U) (hUH : U ≤ H) (hδ : 0 < δ)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ) :
    ‖∑ z ∈ xiLowHeightIndices H, iteratedBoxAverageComplex (s * x) (m + 3)
      (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue z / riemannXiDivisorZeroValue z) x‖ / x ≤
      dusartBoxSplitLowBound m s x₀ a U H δ :=
  norm_dusartBox_low_div_le_split_frozen m hs hx₀ hx ha haU hUH hδ hgap

end PrimeFactorUnimodality.Tests
