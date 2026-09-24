import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserFrozenPointwise
import PrimeFactorUnimodality.Helpers.Analytic.DusartLogarithmicScalars
import PrimeFactorUnimodality.Helpers.Analytic.XiLowReciprocalNormMonotone

/-! # Branch-free logarithmic budgets for the frozen Dusart bound

The global peak dominates either branch of the selected zero-tail majorant.
Writing height powers as exponentials leaves a scalar expression involving
only arithmetic, logarithms, square roots and exponentials. The low-zero
mass uses the already proved allowance of seventy at every smaller height.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- A branch-free upper bound for the closed tail at logarithmic height `L`. -/
def xiRosserLogPeakTail (a q p L : ℝ) : ℝ :=
  2 * (exp (-2 * sqrt (a * (q - p))) *
    (exp ((1 - p) * L) / (2 * π) *
      ((L - log (2 * π)) / (p - 1) + 1 / (p - 1) ^ 2) + exp (-p * L) / p) +
    2 * (L + 17) * exp (-q * L - a / L))

/-- Both branches of the closed tail are controlled by the same peak expression. -/
theorem xiRosserClosedTailBound_le_logPeak {a q p H : ℝ}
    (ha : 0 ≤ a) (hp : 1 < p) (hpq : p ≤ q) (hH : 10 ≤ H) :
    xiRosserClosedTailBound a q p H ≤ xiRosserLogPeakTail a q p (log H) := by
  have hHpos : 0 < H := by linarith
  have hf := logDampedPowerIntegralFactor_nonneg hp (by positivity : 0 < 2 * π)
    (by linarith [pi_lt_four] : 2 * π ≤ H)
  have hm := logDampedPowerMajorant_le_peak ha hpq (by linarith : 1 < H)
  have h := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_right hm hf)
      (le_rfl : 2 * (log H + 17) * logDampedPower a q H ≤ _))
    (by norm_num : (0 : ℝ) ≤ 2)
  convert h using 1
  · rfl
  · simp only [xiRosserLogPeakTail, logDampedPowerIntegralFactor, logDampedPower,
      rpow_def_of_pos hHpos, log_div hHpos.ne' (by positivity : 2 * π ≠ 0)]
    simp only [mul_comm]
    ring

/-- A normalized average budget in the logarithm of the reference point. -/
def dusartFrozenLogAverage (m : ℕ) (s b p H : ℝ) : ℝ :=
  ((1 + (m + 3 : ℕ) * s) * exp (-(1 / 2) * b)) * 70 +
    (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
      xiRosserLogPeakTail (b / 6) (m + 4 : ℕ) p (log H) + 4 * exp (-b)

/-- The original average expression is bounded without a minimum or cutoff branch. -/
theorem dusartBoxRosserFixedRelativeBudget_le_logPeak (m : ℕ) {s x p H : ℝ}
    (hs : 0 < s) (hx : 2 ≤ x) (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (hH : 10 ≤ H) (hH₁ : H ≤ 1000000000) :
    dusartBoxRosserFixedRelativeBudget m s x 6 p 10 H (1 / 2) ≤
      dusartFrozenLogAverage m s (log x) p H := by
  have hxpos : 0 < x := by linarith
  have hl := mul_le_mul_of_nonneg_left
    (xiLowReciprocalNormBound_half_le_of_le_billion hH hH₁)
    (by positivity : 0 ≤ (1 + (m + 3 : ℕ) * s) * exp (-(1 / 2) * log x))
  have ht := xiRosserClosedTailBound_le_logPeak (a := log x / 6)
    (div_nonneg (log_nonneg (by linarith : 1 ≤ x)) (by norm_num)) hp hpq.le hH
  have hh := mul_le_mul_of_nonneg_left ht
    (by positivity : 0 ≤ 2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3))
  have hc : (1 / (2 * (x ^ 2 - 1)) + log (2 * π)) / x ≤ 4 * exp (-log x) := by
    simpa only [exp_neg, exp_log hxpos, div_eq_mul_inv] using dusartLog_correction_le hx
  exact add_le_add (add_le_add hl hh) hc

/-- Both adjacent reference averages, with the exact relative-step rescaling. -/
def dusartFrozenLogPsiBound (m : ℕ) (s b p H : ℝ) : ℝ :=
  let t := 1 - (m + 3 : ℕ) * s
  max (t * dusartFrozenLogAverage m (s / t) (b + log t) p H)
    (dusartFrozenLogAverage m s b p H) + (m + 3 : ℕ) * s / 2

/-- One branch-free scalar expression bounds the entire frozen pointwise budget. -/
theorem dusartRosserFrozenPsiBound_le_logPeak (m : ℕ) {s b p H : ℝ}
    (hs : 0 < s) (hb : 1 ≤ b) (ht : 0 < 1 - (m + 3 : ℕ) * s)
    (hl : 1 ≤ b + log (1 - (m + 3 : ℕ) * s))
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (hH : 10 ≤ H) (hH₁ : H ≤ 1000000000) :
    dusartRosserFrozenPsiBound m s (exp b) 6 p 10 H (1 / 2) ≤
      dusartFrozenLogPsiBound m s b p H := by
  let t := 1 - (m + 3 : ℕ) * s
  have htpos : 0 < t := ht
  have he : log (exp b * t) = b + log t := by
    rw [log_mul (exp_pos b).ne' htpos.ne', log_exp]
  have hx : 2 ≤ exp b := by linarith [add_one_le_exp b]
  have hy : 2 ≤ exp b * t := by
    have h := add_one_le_exp (log (exp b * t))
    rw [exp_log (mul_pos (exp_pos b) htpos), he] at h
    linarith
  have hleft := dusartBoxRosserFixedRelativeBudget_le_logPeak m (div_pos hs htpos)
    hy hp hpq hH hH₁
  rw [he] at hleft
  have hright := dusartBoxRosserFixedRelativeBudget_le_logPeak m hs hx hp hpq hH hH₁
  rw [log_exp] at hright
  exact add_le_add (max_le_max (mul_le_mul_of_nonneg_left hleft htpos.le) hright) le_rfl

end

end PrimeFactorUnimodality
