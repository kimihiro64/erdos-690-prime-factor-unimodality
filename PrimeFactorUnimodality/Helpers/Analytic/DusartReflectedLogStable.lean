import PrimeFactorUnimodality.Helpers.Analytic.DusartFrozenLogStable
import PrimeFactorUnimodality.Helpers.Analytic.DusartReflectedLogBudget

/-! # Stable scaling of both reflected high-tail contributions

The power tail is the zero-damping specialization of the same peak formula.
Its critical-line exponential is combined with the smoothing coefficient
before numerical evaluation, just as for the original region term.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Zero damping at the full power recovers the exact elementary power-tail bound. -/
theorem xiRosserPowerTailBound_eq_logPeak (q : ℝ) {H : ℝ} (hH : 0 < H) :
    xiRosserPowerTailBound q H = xiRosserLogPeakTail 0 q q (log H) := by
  unfold xiRosserPowerTailBound logDampedPowerIntegralFactor
  rw [log_div hH.ne' (by positivity : 2 * π ≠ 0)]
  simp [xiRosserLogPeakTail, logDampedPower, rpow_def_of_pos hH, mul_comm, div_eq_mul_inv]

/-- The scaled power tail reuses the exact zero-damping specialization. -/
theorem exp_mul_xiRosserPowerTailBound (c q : ℝ) {H : ℝ} (hH : 0 < H) :
    exp c * xiRosserPowerTailBound q H = dusartFrozenScaledPeakTail c 0 q q (log H) := by
  rw [xiRosserPowerTailBound_eq_logPeak q hH]
  exact exp_mul_xiRosserLogPeakTail _ _ _ _ _

/-- Both reflected high-tail contributions after their complete exponential scaling. -/
def dusartReflectedLogAverageStable (m : ℕ) (s b p H : ℝ) : ℝ :=
  let c := dusartFrozenLogCoefficient m s
  ((1 + (m + 3 : ℕ) * s) * exp (-(1 / 2) * b)) * 70 +
    (dusartFrozenScaledPeakTail c (b / 6) (m + 4 : ℕ) p (log H) +
      dusartFrozenScaledPeakTail (c - b / 2) 0 (m + 4 : ℕ) (m + 4 : ℕ) (log H)) / 2 +
    4 * exp (-b)

/-- Stable evaluation preserves the entire reflected average exactly. -/
theorem dusartReflectedLogAverage_eq_stable (m : ℕ) {s H : ℝ}
    (hs : 0 < s) (hH : 0 < H) (b p : ℝ) :
    dusartReflectedLogAverage m s b p H = dusartReflectedLogAverageStable m s b p H := by
  have hc := exp_dusartFrozenLogCoefficient m hs
  have hp := exp_mul_xiRosserPowerTailBound (dusartFrozenLogCoefficient m s - b / 2)
    (m + 4 : ℕ) hH
  rw [show dusartFrozenLogCoefficient m s - b / 2 =
    dusartFrozenLogCoefficient m s + (-(1 / 2) * b) by ring, exp_add, hc] at hp
  have hp' : (2 ^ (m + 3) * (1 + (m + 3 : ℕ) * s) ^ (m + 4) / s ^ (m + 3)) *
      (exp (-(1 / 2) * b) * xiRosserPowerTailBound (m + 4 : ℕ) H) =
        dusartFrozenScaledPeakTail (dusartFrozenLogCoefficient m s - b / 2)
          0 (m + 4 : ℕ) (m + 4 : ℕ) (log H) := by
    simpa only [mul_assoc, show dusartFrozenLogCoefficient m s + (-(1 / 2) * b) =
      dusartFrozenLogCoefficient m s - b / 2 by ring] using hp
  unfold dusartReflectedLogAverage dusartReflectedLogAverageStable
  rw [mul_div, mul_add, dusartFrozenCoefficient_mul_logPeakTail m hs, hp']

end

end PrimeFactorUnimodality
