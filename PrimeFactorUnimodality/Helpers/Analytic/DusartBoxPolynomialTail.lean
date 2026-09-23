import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserTail
import PrimeFactorUnimodality.Helpers.Analytic.XiRosserPolynomialTail

/-! # Polynomial parameter decay for the actual normalized high-zero sum

Use the complete actual damped tail and its Taylor majorant. Any natural
polynomial order is available at every arithmetic point above one, without
a turning-point condition. Relative smoothing cancels the arithmetic scale
exactly. The zero-free-region hypothesis is retained explicitly here.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Polynomial decay controls the actual relative high tail for any smoothing and Taylor orders. -/
theorem norm_dusartBoxXiHighSum_div_le_polynomial (m n : ℕ) {s x R T : ℝ}
    (hs : 0 < s) (hx : 1 < x) (hR : 0 < R) (hT : 10 < T)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, T ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|)) :
    ‖dusartBoxXiHighSum m (s * x) x T‖ / x ≤
      (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
        ((n.factorial : ℝ) ^ 2 / (Real.log x / R) ^ n) *
          xiRosserPowerTailBound (m + 3 : ℕ) T := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have ht := xiRosserAbsoluteTail_le_polynomial n (div_pos (Real.log_pos hx) hR)
    (by norm_cast; omega : (3 : ℝ) ≤ (m + 4 : ℕ)) hT
  rw [show ((m + 4 : ℕ) : ℝ) - 1 = (m + 3 : ℕ) by push_cast; ring] at ht
  have hz := norm_dusartBoxXiHighSum_le_actual_tail m (mul_pos hs hxpos) hx hR
    (by linarith : 1 < T) hreg
  have hU : x + (m + 3 : ℕ) * (s * x) = x * (1 + (m + 3 : ℕ) * s) := by ring
  have hC : 2 ^ (m + 3) * (x * (1 + (m + 3 : ℕ) * s)) ^ (m + 4) /
      (s * x) ^ (m + 3) =
      x * (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) := by
    rw [mul_pow, mul_pow, show m + 4 = (m + 3) + 1 by omega, pow_succ x]
    field_simp
  rw [hU, hC] at hz
  apply (div_le_iff₀ hxpos).mpr
  exact (hz.trans (mul_le_mul_of_nonneg_left ht (by positivity))).trans_eq (by ring)

end

end PrimeFactorUnimodality
