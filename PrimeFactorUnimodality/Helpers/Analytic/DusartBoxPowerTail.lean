import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserClosedTail

/-! # A complete high-zero estimate using only the critical strip

Higher-order smoothing makes the zero-damping tail integrable.
The proved critical strip supplies gap zero at every high zero.
Thus this constant relative-error estimate needs no numerical
zero-free region, turning point or auxiliary split exponent.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real intervalIntegral

/-- The full high-zero sum is bounded without a region hypothesis. -/
theorem norm_dusartBoxXiHighSum_le_power (m : ℕ) {h x T : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 10 < T) :
    ‖dusartBoxXiHighSum m h x T‖ ≤
      (2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)) *
        xiRosserPowerTailBound (m + 4 : ℕ) T := by
  let P : RiemannXiDivisorZeroIndex → Prop :=
    fun p => T ≤ |(riemannXiDivisorZeroValue p).im|
  let C := 2 ^ (m + 3) * (x + (m + 3 : ℕ) * h) ^ (m + 4) / h ^ (m + 3)
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq : (2 : ℝ) ≤ (m + 4 : ℕ) := by norm_cast; omega
  have hs := ((summable_dusartBox_xi_power_average m hh hx).subtype P).norm
  have hk := (summable_xi_abs_logDampedPower le_rfl hq (by linarith : 1 < T)
    (P := P) (fun _ hp => hp)).mul_left C
  have hp (p : {p : RiemannXiDivisorZeroIndex // P p}) :
      ‖iteratedBoxAverageComplex h (m + 3)
        (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p.1 / riemannXiDivisorZeroValue p.1) x‖ ≤
        C * logDampedPower 0 (m + 4 : ℕ) |(riemannXiDivisorZeroValue p.1).im| := by
    have hγ : 0 < |(riemannXiDivisorZeroValue p.1).im| :=
      (show 0 < T by linarith).trans_le p.2
    obtain ⟨hβ0, hβ1⟩ := riemannXi_zero_mem_critical_strip (riemannXiDivisorZeroValue_eq_zero p.1)
    have hb := norm_dusartBox_paired_atom_le_height_gap m hh hx le_rfl (abs_pos.mp hγ) hβ0
      (by simpa using hβ1 : (riemannXiDivisorZeroValue p.1).re ≤ 1 - 0)
    rw [finiteLaplace_dusartBoxWeight_add_inv m hh hx (riemannXiDivisorZeroValue_ne_zero p.1)] at hb
    refine hb.trans_eq ?_
    rw [logDampedPower_eq_rpow_mul hγ, Real.rpow_neg hγ.le, Real.rpow_natCast]
    simp only [neg_zero, zero_mul, zero_div, Real.exp_zero, mul_one]
    dsimp [C]
    ring
  calc
    _ ≤ ∑' p : {p : RiemannXiDivisorZeroIndex // P p},
        ‖iteratedBoxAverageComplex h (m + 3)
          (fun t => (t : ℂ) ^ riemannXiDivisorZeroValue p.1 / riemannXiDivisorZeroValue p.1) x‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' p : {p : RiemannXiDivisorZeroIndex // P p},
        C * logDampedPower 0 (m + 4 : ℕ) |(riemannXiDivisorZeroValue p.1).im| :=
      hs.tsum_le_tsum hp hk
    _ = C * xiRosserAbsoluteTail 0 (m + 4 : ℕ) T := by rw [tsum_mul_left]; rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (xiRosserAbsoluteTail_zero_le_power hq hT) hC

/-- With a relative step, the normalized bound is independent of x. -/
theorem norm_dusartBoxXiHighSum_div_le_power (m : ℕ) {s x T : ℝ}
    (hs : 0 < s) (hx : 1 < x) (hT : 10 < T) :
    ‖dusartBoxXiHighSum m (s * x) x T‖ / x ≤
      (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
        xiRosserPowerTailBound (m + 4 : ℕ) T := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have ht := norm_dusartBoxXiHighSum_le_power m (mul_pos hs hxpos) hx hT
  have hU : x + (m + 3 : ℕ) * (s * x) = x * (1 + (m + 3 : ℕ) * s) := by ring
  have hC : 2 ^ (m + 3) * (x * (1 + (m + 3 : ℕ) * s)) ^ (m + 4) /
      (s * x) ^ (m + 3) =
      x * (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) := by
    rw [mul_pow, mul_pow, show m + 4 = (m + 3) + 1 by omega, pow_succ x]
    field_simp
  rw [hU, hC] at ht
  apply (div_le_iff₀ hxpos).mpr
  convert ht using 1
  ring

end

end PrimeFactorUnimodality
