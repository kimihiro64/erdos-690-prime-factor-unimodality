import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxDampedHighTail

/-! # Simultaneous height decay, zero-free damping, and the full high series -/

namespace PrimeFactorUnimodality.Tests

open Complex intervalIntegral

example (m : ℕ) {h x δ : ℝ} (hh : 0 < h) (hx : 1 < x) (hδ : 0 ≤ δ)
    {s : ℂ} (hs : s.im ≠ 0) (hβ0 : 0 ≤ s.re) (hβ : s.re ≤ 1 - δ) :
    ‖finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-s) +
        1 / s‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) /
        (h ^ (m + 3) * |s.im| ^ (m + 4))) * Real.exp (-δ * Real.log x) :=
  norm_dusartBox_paired_atom_le_height_gap m hh hx hδ hs hβ0 hβ

example (m : ℕ) {h x : ℝ} (hh : 0 < h) (hx : 1 < x)
    {s : ℂ} (hs : s.im ≠ 0) (hβ0 : 0 ≤ s.re) (hβ : s.re ≤ 1) :
    ‖finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-s) +
        1 / s‖ ≤
      2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) /
        (h ^ (m + 3) * |s.im| ^ (m + 4)) := by
  simpa only [sub_zero, neg_zero, zero_mul, Real.exp_zero, mul_one] using
    norm_dusartBox_paired_atom_le_height_gap m hh hx le_rfl hs hβ0
      (show s.re ≤ 1 - 0 by simpa using hβ)

example (m : ℕ) {h x T δ : ℝ} (hh : 0 < h) (hx : 1 < x) (hT : 0 < T) (hδ : 0 ≤ δ)
    {s : ℂ} (hβ0 : 0 ≤ s.re) (hβ : s.re ≤ 1 - δ) (hγ : T ≤ |s.im|) :
    ‖finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-s) +
        1 / s‖ ≤ dusartBoxTailFactor m h x T * (Real.exp (-δ * Real.log x) / s.im ^ 2) :=
  norm_dusartBox_paired_atom_le_tail_kernel_gap m hh hx hT hδ hβ0 hβ hγ

example (m : ℕ) {h x T : ℝ} (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T)
    (p : RiemannXiDivisorZeroIndex) (hp : T ≤ |(riemannXiDivisorZeroValue p).im|) :
    ‖iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p / riemannXiDivisorZeroValue p) x‖ ≤
      dusartBoxTailFactor m h x T * xiInitialDampedHeightKernel x p :=
  norm_dusartBox_xi_atom_le_initial_tail_kernel m hh hx hT p hp

example {x T : ℝ} (hx : 1 ≤ x) (hT : 10 ^ 9 ≤ T)
    (p : RiemannXiDivisorZeroIndex) (hp : T ≤ |(riemannXiDivisorZeroValue p).im|) :
    xiInitialDampedHeightKernel x p ≤ 1 / (riemannXiDivisorZeroValue p).im ^ 2 :=
  xiInitialDampedHeightKernel_le_inv_sq hx hT p hp

example {x T : ℝ} (hx : 1 ≤ x) (hT : 10 ^ 9 ≤ T) :
    Summable (fun p : {p : RiemannXiDivisorZeroIndex //
      T ≤ |(riemannXiDivisorZeroValue p).im|} => xiInitialDampedHeightKernel x p.1) :=
  summable_xiInitialDampedHeightKernel hx hT

example {x T : ℝ} (hx : 1 ≤ x) (hT : 10 ^ 9 ≤ T) :
    xiInitialDampedHeightTail x T ≤ xiHeightTail 0 T :=
  xiInitialDampedHeightTail_le_heightTail hx hT

example (m : ℕ) {h x T : ℝ} (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T) :
    ‖dusartBoxXiHighSum m h x T‖ ≤
      dusartBoxTailFactor m h x T * xiInitialDampedHeightTail x T :=
  norm_dusartBoxXiHighSum_le_initialDampedTail m hh hx hT

end PrimeFactorUnimodality.Tests
