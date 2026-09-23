import PrimeFactorUnimodality.Helpers.Analytic.DusartPrimeCountingSquared
import PrimeFactorUnimodality.Helpers.Analytic.DusartShortIntervalSquared

/-! # Exact provider boundaries at the published log-square cutoff

Dusart's HDR Theorem 93 lists theta coefficient 0.2 from 3594641.
Specialize the direct adapters at that point and discharge their elementary
logarithmic side conditions. The theta estimate itself, finite prefixes and
the two explicit prime-counting anchor inequalities remain genuine inputs.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The published starting point is already above the required logarithmic height. -/
theorem dusart_log_squared_cutoff_ge_ten :
    (10 : ℝ) ≤ Real.log 3594641 := by
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ 20)
    (by norm_num : (2 : ℝ) ^ 20 ≤ 3594641)
  rw [Real.log_pow] at hl
  norm_num at hl
  linarith [Real.log_two_gt_d9]

/-- The published theta estimate and a prefix through its cutoff give the exact short interval. -/
theorem hasDusartShortIntervalPrime_of_published_logSquared
    (finite : HasDusartShortIntervalPrimeBelow 3594641)
    (error : HasThetaLogSquaredError (1 / 5) 3594641) : HasDusartShortIntervalPrime :=
  hasDusartShortIntervalPrime_of_thetaLogSquared (by norm_num)
    (by linarith [dusart_log_squared_cutoff_ge_ten]) finite error

/-- The same cutoff suffices for both requested prime-counting bounds, with exact anchors. -/
theorem hasDusartPrimeCountingBounds_of_published_logSquared
    (finite : HasDusartRealPrimeCountingBoundsBelow 3594641)
    (error : HasThetaLogSquaredError (1 / 5) 3594641)
    (lowerAnchor : Chebyshev.theta 3594641 * Real.log 3594641 ^ 2 +
      3594641 * Real.log 3594641 + (1 / 5 : ℝ) * 3594641 ≤
        (Nat.primeCounting 3594641 : ℝ) * Real.log 3594641 ^ 3)
    (upperAnchor : (Nat.primeCounting 3594641 : ℝ) * Real.log 3594641 ^ 3 ≤
      Chebyshev.theta 3594641 * Real.log 3594641 ^ 2 +
        (6381 / 5000 : ℝ) * 3594641 * Real.log 3594641 - (1 / 5 : ℝ) * 3594641) :
    HasDusartPrimeCountingBounds := by
  apply hasDusartPrimeCountingBounds_of_thetaLogSquared (by norm_num)
    dusart_log_squared_cutoff_ge_ten finite error
  · apply (dusartPiLower_le_dusartJ_two_anchor_iff (by norm_num : (1 : ℝ) < 3594641)).mpr
    simpa only [show (3594641 : ℝ) = (3594641 : ℕ) by norm_num, Nat.floor_natCast] using lowerAnchor
  · apply (dusartJ_two_le_dusartPiUpper_anchor_iff (by norm_num : (1 : ℝ) < 3594641)).mpr
    simpa only [show (3594641 : ℝ) = (3594641 : ℕ) by norm_num, Nat.floor_natCast] using upperAnchor

end

end PrimeFactorUnimodality
