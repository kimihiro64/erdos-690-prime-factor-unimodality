import PrimeFactorUnimodality.Helpers.Analytic.DusartFrozenLogBudget

/-! # Exact scaling before evaluation of frozen zero-tail budgets

The smoothing coefficient is large while the tail exponentials are small.
Combining their exponents before interval rounding avoids amplifying the
rounding error of an intermediate tiny tail. All identities are exact;
neither the mathematical bound nor the required precision is assumed.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The logarithm of the complete smoothing coefficient. -/
def dusartFrozenLogCoefficient (m : ℕ) (s : ℝ) : ℝ :=
  (m + 3 : ℕ) * log 2 + (m + 4 : ℕ) * log (1 + (m + 3 : ℕ) * s) -
    (m + 3 : ℕ) * log s

/-- Exponentiating recovers every factor in the original coefficient. -/
theorem exp_dusartFrozenLogCoefficient (m : ℕ) {s : ℝ} (hs : 0 < s) :
    exp (dusartFrozenLogCoefficient m s) =
      2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3) := by
  have hw : 0 < 1 + (m + 3 : ℕ) * s := by positivity
  have hlog : log (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) =
      dusartFrozenLogCoefficient m s := by
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_pow, log_pow, log_pow]
    rfl
  rw [← hlog, exp_log (by positivity)]

/-- The density, reciprocal-height and counting-boundary contributions after scaling. -/
def dusartFrozenScaledPeakTail (c a q p L : ℝ) : ℝ :=
  2 * (exp (c - 2 * sqrt (a * (q - p)) + (1 - p) * L) / (2 * π) *
      ((L - log (2 * π)) / (p - 1) + 1 / (p - 1) ^ 2) +
    exp (c - 2 * sqrt (a * (q - p)) - p * L) / p +
    2 * (L + 17) * exp (c - q * L - a / L))

/-- Scaling the closed expression is exactly addition inside its exponentials. -/
theorem exp_mul_xiRosserLogPeakTail (c a q p L : ℝ) :
    exp c * xiRosserLogPeakTail a q p L = dusartFrozenScaledPeakTail c a q p L := by
  unfold xiRosserLogPeakTail dusartFrozenScaledPeakTail
  simp only [neg_mul, exp_add, exp_sub, exp_neg]
  ring

/-- The entire smoothing coefficient is absorbed without changing the tail value. -/
theorem dusartFrozenCoefficient_mul_logPeakTail (m : ℕ) {s : ℝ} (hs : 0 < s)
    (a q p L : ℝ) :
    (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
      xiRosserLogPeakTail a q p L =
        dusartFrozenScaledPeakTail (dusartFrozenLogCoefficient m s) a q p L := by
  rw [← exp_dusartFrozenLogCoefficient m hs]
  exact exp_mul_xiRosserLogPeakTail _ _ _ _ _

/-- A normalized average with the high-tail multiplication already combined. -/
def dusartFrozenLogAverageStable (m : ℕ) (s b p H : ℝ) : ℝ :=
  ((1 + (m + 3 : ℕ) * s) * exp (-(1 / 2) * b)) * 70 +
    dusartFrozenScaledPeakTail (dusartFrozenLogCoefficient m s)
      (b / 6) (m + 4 : ℕ) p (log H) + 4 * exp (-b)

/-- The stable scalar expression is the original branch-free average, not a replacement bound. -/
theorem dusartFrozenLogAverage_eq_stable (m : ℕ) {s : ℝ} (hs : 0 < s) (b p H : ℝ) :
    dusartFrozenLogAverage m s b p H = dusartFrozenLogAverageStable m s b p H := by
  unfold dusartFrozenLogAverage dusartFrozenLogAverageStable
  rw [dusartFrozenCoefficient_mul_logPeakTail m hs]

end

end PrimeFactorUnimodality
