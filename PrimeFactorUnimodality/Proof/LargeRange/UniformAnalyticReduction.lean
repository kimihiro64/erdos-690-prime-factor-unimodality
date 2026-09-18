import PrimeFactorUnimodality.Helpers.Analytic.ReciprocalPrimeBounds
import PrimeFactorUnimodality.Proof.LargeRange.UniformValley

set_option autoImplicit false

/-! # Analytic reduction for the uniform tail -/

namespace PrimeFactorUnimodality

noncomputable section

/-- The uniform construction reduced to explicit logarithmic inequalities.
The Meissel--Mertens constant cancels entirely from the descent shell; it is
needed only as a one-sided bound for the later ascent. -/
theorem uniformConstruction_not_isUnimodal_of_mertens_bounds
    {qPrev q k bound target : Nat} {mertens errorConstant : Real}
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (reciprocalEstimate :
      HasReciprocalPrimeEstimate mertens errorConstant)
    (consecutive : ConsecutivePrimes qPrev q)
    (qPrev_gt_two : 2 < qPrev)
    (hk : 4 ≤ k)
    (bound_pos : 1 ≤ bound)
    (primorial_large : 599 ≤ 9 * primorial q)
    (target_pos : 1 ≤ target)
    (shellNumeric :
      (target : Real) <
        dusartPiLower (9 * primorial q) -
          dusartPiUpper (4 * primorial q))
    (widthNumeric : 5 * primorial q < target * bound)
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (2 * primorial q + 1) - 1)
    (prefix_le_primorial : primeAt (k - 2) - 1 ≤ primorial q)
    (descentNumeric :
      ((k - 1 : Nat) : Real) < ((2 * qPrev + 1 : Nat) : Real) *
        (Real.log (Real.log ((primorial q : Nat) : Real)) -
          Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) -
          errorConstant / Real.log ((primorial q : Nat) : Real) -
          errorConstant / Real.log ((primeAt (k - 2) - 1 : Nat) : Real)))
    (ascentNumeric :
      (bound : Real) *
          (Real.log (Real.log ((9 * primorial q : Nat) : Real)) + mertens +
            errorConstant / Real.log ((9 * primorial q : Nat) : Real) + 1) <
        ((k - 1 : Nat) : Real)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let x := primeAt (k - 2) - 1
  let P := primorial q
  have x_two : 2 ≤ x := by
    have primeFive : 5 ≤ primeAt (k - 2) := by
      have indexTwo : 2 ≤ k - 2 := by omega
      have := primeAt_strictMono.monotone indexTwo
      norm_num [primeAt] at this ⊢
      exact this
    dsimp only [x]
    omega
  have P_two : 2 ≤ P := by
    have := primorial_large
    dsimp only [P]
    omega
  have x_le_P : x ≤ P := by
    simpa only [x, P] using prefix_le_primorial
  have descentWeight :
      ((k - 1 : Nat) : Real) < ((2 * qPrev + 1 : Nat) : Real) *
        (primeWeightSumBelow (P + 1) -
          primeWeightSumBelow (primeAt (k - 2))) := by
    have shellLower := primeWeightSumBelow_sub_lower_of_estimate_of_le
      reciprocalEstimate x_two P_two x_le_P
    have cutoffEq : x + 1 = primeAt (k - 2) := by
      dsimp only [x]
      have := one_lt_primeAt (k - 2)
      omega
    rw [cutoffEq] at shellLower
    have thresholdNonneg : (0 : Real) ≤ ((2 * qPrev + 1 : Nat) : Real) := by
      positivity
    exact descentNumeric.trans_le
      (mul_le_mul_of_nonneg_left shellLower thresholdNonneg)
  have ascentWeight :
      (bound : Real) * primeWeightSumBelow (9 * P + 1) <
        ((k - 1 : Nat) : Real) := by
    have sumUpper := primeWeightSumBelow_upper_of_estimate
      reciprocalEstimate (show 2 ≤ 9 * P by omega)
    have boundNonneg : (0 : Real) ≤ (bound : Real) := by positivity
    exact (mul_le_mul_of_nonneg_left sumUpper boundNonneg).trans_lt
      (by simpa only [P] using ascentNumeric)
  exact uniformConstruction_not_isUnimodal_of_weight_bounds
    primeCountingBounds consecutive qPrev_gt_two (by omega) bound_pos
    primorial_large target_pos shellNumeric widthNumeric descentDefined
    (by simpa only [P] using descentWeight)
    (by simpa only [P] using ascentWeight)

/-- Uniform-tail reduction using Dusart's sharp reciprocal-prime error.  The
upper estimate is required only at the earlier prime cutoff and at `8P`; the
lower estimate at `P` uses its wider `x > 1` domain. -/
theorem uniformConstruction_not_isUnimodal_of_dusart_reciprocal
    {qPrev q k bound target : Nat} {mertens : Real}
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (reciprocalEstimate : HasDusartReciprocalPrimeEstimate mertens)
    (consecutive : ConsecutivePrimes qPrev q)
    (qPrev_gt_two : 2 < qPrev)
    (hk : 4 ≤ k)
    (bound_pos : 1 ≤ bound)
    (primorial_large : 599 ≤ 9 * primorial q)
    (ascentThreshold : 10372 ≤ 9 * primorial q)
    (target_pos : 1 ≤ target)
    (shellNumeric :
      (target : Real) <
        dusartPiLower (9 * primorial q) - dusartPiUpper (4 * primorial q))
    (widthNumeric : 5 * primorial q < target * bound)
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (2 * primorial q + 1) - 1)
    (prefixThreshold : 10372 ≤ primeAt (k - 2) - 1)
    (prefix_le_primorial : primeAt (k - 2) - 1 ≤ primorial q)
    (descentNumeric :
      ((k - 1 : Nat) : Real) < ((2 * qPrev + 1 : Nat) : Real) *
        (Real.log (Real.log ((primorial q : Nat) : Real)) -
          Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) -
          dusartReciprocalError (((primorial q : Nat) : Real)) -
          dusartReciprocalError
            (((primeAt (k - 2) - 1 : Nat) : Real))))
    (ascentNumeric :
      (bound : Real) *
          (Real.log (Real.log ((9 * primorial q : Nat) : Real)) + mertens +
            dusartReciprocalError (((9 * primorial q : Nat) : Real)) + 1) <
        ((k - 1 : Nat) : Real)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let x := primeAt (k - 2) - 1
  let P := primorial q
  have P_two : 2 ≤ P := by
    have := primorial_large
    dsimp only [P]
    omega
  have x_le_P : x ≤ P := by
    simpa only [x, P] using prefix_le_primorial
  have descentWeight :
      ((k - 1 : Nat) : Real) < ((2 * qPrev + 1 : Nat) : Real) *
        (primeWeightSumBelow (P + 1) -
          primeWeightSumBelow (primeAt (k - 2))) := by
    have shellLower := primeWeightSumBelow_sub_lower_of_dusart
      reciprocalEstimate (by simpa only [x] using prefixThreshold) P_two x_le_P
    have cutoffEq : x + 1 = primeAt (k - 2) := by
      dsimp only [x]
      have := one_lt_primeAt (k - 2)
      omega
    rw [cutoffEq] at shellLower
    have thresholdNonneg : (0 : Real) ≤ ((2 * qPrev + 1 : Nat) : Real) := by
      positivity
    exact descentNumeric.trans_le
      (mul_le_mul_of_nonneg_left shellLower thresholdNonneg)
  have ascentWeight :
      (bound : Real) * primeWeightSumBelow (9 * P + 1) <
        ((k - 1 : Nat) : Real) := by
    have sumUpper := primeWeightSumBelow_upper_of_dusart reciprocalEstimate
      (by simpa only [P] using ascentThreshold)
    have boundNonneg : (0 : Real) ≤ (bound : Real) := by positivity
    exact (mul_le_mul_of_nonneg_left sumUpper boundNonneg).trans_lt
      (by simpa only [P] using ascentNumeric)
  exact uniformConstruction_not_isUnimodal_of_weight_bounds
    primeCountingBounds consecutive qPrev_gt_two (by omega) bound_pos
    primorial_large target_pos shellNumeric widthNumeric descentDefined
    (by simpa only [P] using descentWeight)
    (by simpa only [P] using ascentWeight)

/-- Direct-shell version of the sharp reciprocal-prime reduction. -/
theorem uniformConstruction_not_isUnimodal_of_dusart_reciprocal_direct
    {qPrev q k bound : Nat} {mertens : Real}
    (primeCountingBounds : HasDusartPrimeCountingBounds)
    (reciprocalEstimate : HasDusartReciprocalPrimeEstimate mertens)
    (consecutive : ConsecutivePrimes qPrev q)
    (qPrev_gt_two : 2 < qPrev)
    (hk : 4 ≤ k)
    (bound_pos : 1 ≤ bound)
    (primorial_large : 599 ≤ 9 * primorial q)
    (ascentThreshold : 10372 ≤ 9 * primorial q)
    (shellNumeric :
      ((5 * primorial q : Nat) : Real) / bound + 1 <
        dusartPiLower (9 * primorial q) - dusartPiUpper (4 * primorial q))
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (2 * primorial q + 1) - 1)
    (prefixThreshold : 10372 ≤ primeAt (k - 2) - 1)
    (prefix_le_primorial : primeAt (k - 2) - 1 ≤ primorial q)
    (descentNumeric :
      ((k - 1 : Nat) : Real) < ((2 * qPrev + 1 : Nat) : Real) *
        (Real.log (Real.log ((primorial q : Nat) : Real)) -
          Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) -
          dusartReciprocalError (((primorial q : Nat) : Real)) -
          dusartReciprocalError
            (((primeAt (k - 2) - 1 : Nat) : Real))))
    (ascentNumeric :
      (bound : Real) *
          (Real.log (Real.log ((9 * primorial q : Nat) : Real)) + mertens +
            dusartReciprocalError (((9 * primorial q : Nat) : Real)) + 1) <
        ((k - 1 : Nat) : Real)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let x := primeAt (k - 2) - 1
  let P := primorial q
  have P_two : 2 ≤ P := by
    have := primorial_large
    dsimp only [P]
    omega
  have x_le_P : x ≤ P := by simpa only [x, P] using prefix_le_primorial
  have descentWeight :
      ((k - 1 : Nat) : Real) < ((2 * qPrev + 1 : Nat) : Real) *
        (primeWeightSumBelow (P + 1) -
          primeWeightSumBelow (primeAt (k - 2))) := by
    have shellLower := primeWeightSumBelow_sub_lower_of_dusart
      reciprocalEstimate (by simpa only [x] using prefixThreshold) P_two x_le_P
    have cutoffEq : x + 1 = primeAt (k - 2) := by
      dsimp only [x]
      have := one_lt_primeAt (k - 2)
      omega
    rw [cutoffEq] at shellLower
    have thresholdNonneg : (0 : Real) ≤ ((2 * qPrev + 1 : Nat) : Real) := by
      positivity
    exact descentNumeric.trans_le
      (mul_le_mul_of_nonneg_left shellLower thresholdNonneg)
  have ascentWeight :
      (bound : Real) * primeWeightSumBelow (9 * P + 1) <
        ((k - 1 : Nat) : Real) := by
    have sumUpper := primeWeightSumBelow_upper_of_dusart reciprocalEstimate
      (by simpa only [P] using ascentThreshold)
    have boundNonneg : (0 : Real) ≤ (bound : Real) := by positivity
    exact (mul_le_mul_of_nonneg_left sumUpper boundNonneg).trans_lt
      (by simpa only [P] using ascentNumeric)
  exact uniformConstruction_not_isUnimodal_of_weight_bounds_direct
    primeCountingBounds consecutive qPrev_gt_two (by omega) bound_pos
    primorial_large shellNumeric descentDefined
    (by simpa only [P] using descentWeight)
    (by simpa only [P] using ascentWeight)

end

end PrimeFactorUnimodality
