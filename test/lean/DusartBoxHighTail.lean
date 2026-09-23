import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxZeroSplit

/-! # Quantitative box-tail and cutoff regressions

Keep both signs of the ordinate, include zeros at the high cutoff, and
exercise the exact split also at cutoff zero. No low-height location
fact is silently supplied by these tests.
-/

namespace PrimeFactorUnimodality.Tests

open Complex intervalIntegral

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) {s : ℂ} (hs : s.im ≠ 0)
    (hβ0 : 0 ≤ s.re) (hβ1 : s.re ≤ 1) :
    ‖finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-s) +
        1 / s‖ ≤ 2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) /
          (h ^ (m + 3) * |s.im| ^ (m + 4)) :=
  norm_dusartBox_paired_atom_le_height m hh hx hs hβ0 hβ1

example (m : ℕ) {h x T : ℝ} (hh : 0 < h) (hx : 1 < x) (hT : 0 < T)
    {s : ℂ} (hβ0 : 0 ≤ s.re) (hβ1 : s.re ≤ 1) (hγ : T = |s.im|) :
    ‖finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-s) +
      1 / s‖ ≤ dusartBoxTailFactor m h x T * (1 / s.im ^ 2) :=
  norm_dusartBox_paired_atom_le_tail_kernel m hh hx hT hβ0 hβ1 hγ.le

example (T : ℝ) : xiHeightTail 0 T =
    ∑' p : {p : RiemannXiDivisorZeroIndex // T ≤ |(riemannXiDivisorZeroValue p).im|},
      1 / (riemannXiDivisorZeroValue p.1).im ^ 2 := xiHeightTail_zero_eq_tsum T

example {T : ℝ} (hT : 0 < T) : xiHeightTail 0 T ≤ 4 * xiHeightTail (T / 2) (T / 2) :=
  xiHeightTail_zero_le_half_shift hT

example {T : ℝ} (hT : 10 ^ 9 ≤ T) :
    xiHeightTail 0 T ≤ 4 * xiLehmanHighBound (T / 2) (T / 2) :=
  xiHeightTail_zero_le_highBound hT

example (m : ℕ) {h x T : ℝ} (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T) :
    ‖dusartBoxXiHighSum m h x T‖ ≤
      dusartBoxTailFactor m h x T * (4 * xiLehmanHighBound (T / 2) (T / 2)) :=
  norm_dusartBoxXiHighSum_le_highBound m hh hx hT

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x) :
    smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) 0 =
      dusartBoxXiHighSum m h x 0 := by
  have hS : xiLowHeightIndices 0 = ∅ := by
    apply Finset.ext
    intro p
    simp only [mem_xiLowHeightIndices, Finset.notMem_empty, iff_false, not_lt]
    exact abs_nonneg _
  rw [smoothedXiPairedSum_box_eq_low_add_high m hh hx 0, hS]
  simp

example (m : ℕ) {h x T δ : ℝ} (hh : 0 < h) (hx : 1 < x)
    (hT : 10 ^ 9 ≤ T) (hδ : 0 ≤ δ)
    (hg : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re ≤ 1 - δ) :
    ‖smoothedXiPairedSum (fun u => (dusartBoxWeight m h x u : ℂ))
        (dusartBoxSupport m h x) 0‖ ≤
      ((x + (m + 3 : ℕ) * h) * Real.exp (-δ * Real.log x)) *
        (∑ p ∈ xiLowHeightIndices T, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) +
      dusartBoxTailFactor m h x T * (4 * xiLehmanHighBound (T / 2) (T / 2)) :=
  norm_smoothedXiPairedSum_box_le_low_gap_add_high m hh hx hT hδ hg

end PrimeFactorUnimodality.Tests
