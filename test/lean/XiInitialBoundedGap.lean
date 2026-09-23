import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxInitialBudget
import PrimeFactorUnimodality.Helpers.Analytic.KadiriInitialLowGap

/-! # Unconditional unit-height exclusion, bounded gap, and actual initial box bounds -/

namespace PrimeFactorUnimodality.Tests

open Chebyshev Complex

example : (∑' p : RiemannXiDivisorZeroIndex, (1 / riemannXiDivisorZeroValue p).re) < 1 / 3 :=
  tsum_re_xi_divisor_reciprocal_lt_third

example (p : RiemannXiDivisorZeroIndex) : 1 < |(riemannXiDivisorZeroValue p).im| :=
  one_lt_abs_im_xi_divisor p

example {ρ : ℂ} (hρ : riemannXi ρ = 0) : 1 < |ρ.im| := one_lt_abs_im_of_xi_zero hρ

example {ρ : ℂ} (hρ : |ρ.im| ≤ 1) : riemannXi ρ ≠ 0 :=
  fun hz => (not_lt_of_ge hρ) (one_lt_abs_im_of_xi_zero hz)

example {T : ℝ} (hT : 10 ^ 9 ≤ T) {ρ : ℂ} (hρ : riemannXi ρ = 0)
    (ht : |ρ.im| ≤ T) : 1 / (56 * Real.log T) ≤ 1 - ρ.re := xi_zero_gap_bounded hT hρ ht

example {ρ : ℂ} (hρ : riemannXi ρ = 0) :
    1 / (56 * Real.log (max (10 ^ 9) |ρ.im|)) ≤ 1 - ρ.re :=
  xi_zero_gap_initial_all_heights hρ

example {H : ℝ} (hH : 10 ^ 9 ≤ H) (p : RiemannXiDivisorZeroIndex)
    (hp : p ∈ xiLowHeightIndices H) :
    (riemannXiDivisorZeroValue p).re ≤ 1 - 1 / (56 * Real.log H) :=
  xi_low_re_le_initial_gap hH p hp

example {n : ℕ} (hn : 1 ≤ n) {H T : ℝ} (hH : 0 ≤ H) (hT : 10 ^ 9 ≤ T)
    (p : RiemannXiDivisorZeroIndex) (hp : |(riemannXiDivisorZeroValue p).im| < T) :
    (riemannXiDivisorZeroValue p).re ≤ kadiriBootstrapSigma 56 n H T :=
  xi_low_re_le_kadiri_initial_sigma hn hH hT p hp

example {a H : ℝ} (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) :
    (∑ p ∈ xiLowHeightIndices H, ‖(1 : ℂ) / riemannXiDivisorZeroValue p‖) ≤
      xiLowReciprocalNormBound a H (1 / (56 * Real.log H)) :=
  sum_xi_low_reciprocal_norm_le_initial ha haH hH

example (m : ℕ) {h x a H T B : ℝ}
    (hh : 0 < h) (hx : 1 < x) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hTB : T ≤ B) :
    |dusartPsiAverageError (m + 3) h x| ≤
      dusartBoxDampedErrorBudget m h x a H T B (1 / (56 * Real.log H)) :=
  abs_dusartPsiAverageError_le_initialBudget m hh hx ha haH hH hHT hTB

example (m : ℕ) {h x a H T B : ℝ}
    (hh : 0 < h) (hx : 1 < x - (m + 3 : ℕ) * h) (ha : 10 ≤ a) (haH : a < H)
    (hH : 10 ^ 9 ≤ H) (hHT : H ≤ T) (hTB : T ≤ B) :
    |ψ x - x| ≤
      max (dusartBoxDampedErrorBudget m h (x - (m + 3 : ℕ) * h) a H T B
        (1 / (56 * Real.log H)))
        (dusartBoxDampedErrorBudget m h x a H T B (1 / (56 * Real.log H))) +
      (m + 3 : ℕ) * h / 2 := abs_psi_sub_le_dusartBoxInitialBudget m hh hx ha haH hH hHT hTB

example {A X H : ℝ} (hH : 10 ^ 9 ≤ H)
    (h : HasDusartDampedScalarBudget A X H (1 / (56 * Real.log H))) :
    HasPsiLogFourthError A X := hasPsiLogFourthError_of_initialBudget hH h

end PrimeFactorUnimodality.Tests
