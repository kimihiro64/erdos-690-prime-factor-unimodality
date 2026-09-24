import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxReflectedPointwise
import PrimeFactorUnimodality.Helpers.Analytic.DusartFrozenLogBudget

/-! # Logarithmic scalar budgets retaining reflected high-zero damping

The original branch-free peak bound controls one half of the reflected
tail. The other half keeps its critical-line exponential and full power
tail. Low-zero mass, correction terms and both adjacent averages remain.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The normalized reflected average in logarithmic coordinates. -/
def dusartReflectedLogAverage (m : ℕ) (s b p H : ℝ) : ℝ :=
  ((1 + (m + 3 : ℕ) * s) * exp (-(1 / 2) * b)) * 70 +
    (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
      ((xiRosserLogPeakTail (b / 6) (m + 4 : ℕ) p (log H) +
        exp (-(1 / 2) * b) * xiRosserPowerTailBound (m + 4 : ℕ) H) / 2) +
    4 * exp (-b)

/-- The branch-free scalar bounds the complete reflected average, including its power term. -/
theorem dusartReflectedRelativeBudget_le_logPeak (m : ℕ) {s x p H : ℝ}
    (hs : 0 < s) (hx : 2 ≤ x) (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (hH : 10 ≤ H) (hH₁ : H ≤ 1000000000) :
    dusartReflectedRelativeBudget m s x 6 p 10 H (1 / 2) ≤
      dusartReflectedLogAverage m s (log x) p H := by
  have hxpos : 0 < x := by linarith
  have hl := mul_le_mul_of_nonneg_left
    (xiLowReciprocalNormBound_half_le_of_le_billion hH hH₁)
    (by positivity : 0 ≤ (1 + (m + 3 : ℕ) * s) * exp (-(1 / 2) * log x))
  have ht := xiRosserClosedTailBound_le_logPeak (a := log x / 6)
    (div_nonneg (log_nonneg (by linarith : 1 ≤ x)) (by norm_num)) hp hpq.le hH
  have hh := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right
      (add_le_add ht (le_refl
        (exp (-(1 / 2) * log x) * xiRosserPowerTailBound (m + 4 : ℕ) H)))
      (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity : 0 ≤ 2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3))
  have hc : (1 / (2 * (x ^ 2 - 1)) + log (2 * π)) / x ≤ 4 * exp (-log x) := by
    simpa only [exp_neg, exp_log hxpos, div_eq_mul_inv] using dusartLog_correction_le hx
  exact add_le_add (add_le_add hl hh) hc

/-- The exact shifted average and smoothing loss are retained in logarithmic coordinates. -/
def dusartReflectedLogPsiBound (m : ℕ) (s b p H : ℝ) : ℝ :=
  let t := 1 - (m + 3 : ℕ) * s
  max (t * dusartReflectedLogAverage m (s / t) (b + log t) p H)
    (dusartReflectedLogAverage m s b p H) + (m + 3 : ℕ) * s / 2

/-- Two logarithmic scalar evaluations bound the actual reflected pointwise budget. -/
theorem dusartReflectedFrozenPsiBound_le_logPeak (m : ℕ) {s b p H : ℝ}
    (hs : 0 < s) (hb : 1 ≤ b) (ht : 0 < 1 - (m + 3 : ℕ) * s)
    (hl : 1 ≤ b + log (1 - (m + 3 : ℕ) * s))
    (hp : 1 < p) (hpq : p < (m + 4 : ℕ))
    (hH : 10 ≤ H) (hH₁ : H ≤ 1000000000) :
    dusartReflectedFrozenPsiBound m s (exp b) 6 p 10 H (1 / 2) ≤
      dusartReflectedLogPsiBound m s b p H := by
  let t := 1 - (m + 3 : ℕ) * s
  have htpos : 0 < t := ht
  have he : log (exp b * t) = b + log t := by
    rw [log_mul (exp_pos b).ne' htpos.ne', log_exp]
  have hx : 2 ≤ exp b := by linarith [add_one_le_exp b]
  have hy : 2 ≤ exp b * t := by
    have h := add_one_le_exp (log (exp b * t))
    rw [exp_log (mul_pos (exp_pos b) htpos), he] at h
    linarith
  have hleft := dusartReflectedRelativeBudget_le_logPeak m (div_pos hs htpos)
    hy hp hpq hH hH₁
  rw [he] at hleft
  have hright := dusartReflectedRelativeBudget_le_logPeak m hs hx hp hpq hH hH₁
  rw [log_exp] at hright
  exact add_le_add (max_le_max (mul_le_mul_of_nonneg_left hleft htpos.le) hright) le_rfl

end

end PrimeFactorUnimodality
