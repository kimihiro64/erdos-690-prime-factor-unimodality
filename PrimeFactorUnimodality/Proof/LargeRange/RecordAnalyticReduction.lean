import PrimeFactorUnimodality.Helpers.Analytic.ReciprocalPrimeBounds
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapClosed
import PrimeFactorUnimodality.Proof.LargeRange.RecordRatioReduction

set_option autoImplicit false

/-! # Analytic reduction for the certified record inputs -/

namespace PrimeFactorUnimodality

noncomputable section

/-- Reduce the record-gap/twin valley to two explicit logarithmic inequalities.
The gap endpoint itself need not be prime: the certified block and Bertrand's
postulate supply the lower prime frontier used here. -/
theorem recordInputs_not_isUnimodal_of_mertens_bounds
    {mertens errorConstant : Real} (k : Nat) (hk : 4 ≤ k)
    (reciprocalEstimate :
      HasReciprocalPrimeEstimate mertens errorConstant)
    (twin : ConsecutivePrimes recordLower recordUpper)
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (recordGapCenter - 86399) - 1)
    (ascentDefined : k - 1 ≤ Nat.primeCounting' recordLower)
    (prefix_le_half :
      primeAt (k - 2) - 1 ≤ (recordGapCenter - 86399) / 2)
    (descentNumeric :
      ((k - 1 : Nat) : Real) < 4753 *
        (Real.log (Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real)) -
          Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) -
          errorConstant /
            Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real) -
          errorConstant / Real.log ((primeAt (k - 2) - 1 : Nat) : Real)))
    (ascentNumeric :
      3 * (Real.log (Real.log ((recordLower - 1 : Nat) : Real)) +
          mertens + errorConstant / Real.log ((recordLower - 1 : Nat) : Real) + 1) <
        ((k - 1 : Nat) : Real)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let x := primeAt (k - 2) - 1
  let y := (recordGapCenter - 86399) / 2
  have x_two : 2 ≤ x := by
    have primeFive : 5 ≤ primeAt (k - 2) := by
      have indexTwo : 2 ≤ k - 2 := by omega
      have := primeAt_strictMono.monotone indexTwo
      norm_num [primeAt] at this ⊢
      exact this
    dsimp only [x]
    omega
  have y_two : 2 ≤ y := by
    dsimp only [y]
    have := recordGapCenter_large
    omega
  have x_le_y : x ≤ y := by simpa only [x, y] using prefix_le_half
  have shellLower := primeWeightSumBelow_sub_lower_of_estimate_of_le
    reciprocalEstimate x_two y_two x_le_y
  have xCutoff : x + 1 = primeAt (k - 2) := by
    dsimp only [x]
    have := one_lt_primeAt (k - 2)
    omega
  rw [xCutoff] at shellLower
  have yCutoff : y + 1 ≤
      primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1) := by
    exact Nat.add_one_le_iff.mpr (by
      simpa only [y] using recordGap_predecessor_gt_half)
  have fullLower := primeWeightSumBelow_mono yCutoff
  have descentWeight :
      ((k - 1 : Nat) : Real) < 4753 *
        (primeWeightSumBelow
            (primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1)) -
          primeWeightSumBelow (primeAt (k - 2))) := by
    have shellToFull :
        primeWeightSumBelow (y + 1) -
            primeWeightSumBelow (primeAt (k - 2)) ≤
          primeWeightSumBelow
              (primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1)) -
            primeWeightSumBelow (primeAt (k - 2)) := by
      linarith
    have numeric :
        ((k - 1 : Nat) : Real) < 4753 *
          (Real.log (Real.log (y : Real)) -
            Real.log (Real.log (x : Real)) -
            errorConstant / Real.log (y : Real) -
            errorConstant / Real.log (x : Real)) := by
      simpa only [x, y] using descentNumeric
    linarith [shellLower, shellToFull]
  have recordPredTwo : 2 ≤ recordLower - 1 := by
    have lower_ne_two : recordLower ≠ 2 := by
      intro lower_eq
      have product_eq : recordFactor * (recordFactor - 1) = 3 := by
        rw [← recordLower_add_one, lower_eq]
      have evenProduct := Nat.even_mul_pred_self recordFactor
      rw [product_eq] at evenProduct
      rcases evenProduct with ⟨half, half_eq⟩
      omega
    have := recordLower_gt_one
    omega
  have ascentUpper := primeWeightSumBelow_upper_of_estimate
    reciprocalEstimate recordPredTwo
  have recordCutoff : recordLower - 1 + 1 = recordLower := by
    have := recordLower_gt_one
    omega
  rw [recordCutoff] at ascentUpper
  have ascentWeight :
      3 * primeWeightSumBelow recordLower < ((k - 1 : Nat) : Real) := by
    have numeric :
        3 * (Real.log (Real.log ((recordLower - 1 : Nat) : Real)) +
            mertens + errorConstant / Real.log ((recordLower - 1 : Nat) : Real) + 1) <
          ((k - 1 : Nat) : Real) := ascentNumeric
    linarith [ascentUpper, numeric]
  exact recordInputs_not_isUnimodal_of_primeWeightSum_bounds k (by omega)
    recordGap_primeGap_ge twin descentDefined ascentDefined descentWeight ascentWeight

/-- The record-input reduction using Dusart's sharp asymmetric reciprocal
prime error.  This is the form needed near the optimized finite/uniform
cutoff, where a coarse `O(1 / log x)` error loses too much margin. -/
theorem recordInputs_not_isUnimodal_of_dusart_reciprocal
    {mertens : Real} (k : Nat) (hk : 4 ≤ k)
    (reciprocalEstimate : HasDusartReciprocalPrimeEstimate mertens)
    (twin : ConsecutivePrimes recordLower recordUpper)
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (recordGapCenter - 86399) - 1)
    (ascentDefined : k - 1 ≤ Nat.primeCounting' recordLower)
    (prefixThreshold : 10372 ≤ primeAt (k - 2) - 1)
    (recordThreshold : 10372 ≤ recordLower - 1)
    (prefix_le_half :
      primeAt (k - 2) - 1 ≤ (recordGapCenter - 86399) / 2)
    (descentNumeric :
      ((k - 1 : Nat) : Real) < 4753 *
        (Real.log (Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real)) -
          Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) -
          dusartReciprocalError
            ((((recordGapCenter - 86399) / 2 : Nat) : Real)) -
          dusartReciprocalError (((primeAt (k - 2) - 1 : Nat) : Real))))
    (ascentNumeric :
      3 * (Real.log (Real.log ((recordLower - 1 : Nat) : Real)) +
          mertens +
            dusartReciprocalError (((recordLower - 1 : Nat) : Real)) + 1) <
        ((k - 1 : Nat) : Real)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let x := primeAt (k - 2) - 1
  let y := (recordGapCenter - 86399) / 2
  have y_two : 2 ≤ y := by
    dsimp only [y]
    have := recordGapCenter_large
    omega
  have x_le_y : x ≤ y := by simpa only [x, y] using prefix_le_half
  have shellLower := primeWeightSumBelow_sub_lower_of_dusart
    reciprocalEstimate (by simpa only [x] using prefixThreshold) y_two x_le_y
  have xCutoff : x + 1 = primeAt (k - 2) := by
    dsimp only [x]
    have := one_lt_primeAt (k - 2)
    omega
  rw [xCutoff] at shellLower
  have yCutoff : y + 1 ≤
      primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1) :=
    Nat.add_one_le_iff.mpr (by
      simpa only [y] using recordGap_predecessor_gt_half)
  have fullLower := primeWeightSumBelow_mono yCutoff
  have descentWeight :
      ((k - 1 : Nat) : Real) < 4753 *
        (primeWeightSumBelow
            (primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1)) -
          primeWeightSumBelow (primeAt (k - 2))) := by
    have shellToFull :
        primeWeightSumBelow (y + 1) -
            primeWeightSumBelow (primeAt (k - 2)) ≤
          primeWeightSumBelow
              (primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1)) -
            primeWeightSumBelow (primeAt (k - 2)) := by
      linarith
    have numeric :
        ((k - 1 : Nat) : Real) < 4753 *
          (Real.log (Real.log (y : Real)) - Real.log (Real.log (x : Real)) -
            dusartReciprocalError y - dusartReciprocalError x) := by
      simpa only [x, y] using descentNumeric
    linarith [shellLower, shellToFull]
  have ascentUpper := primeWeightSumBelow_upper_of_dusart
    reciprocalEstimate recordThreshold
  have recordCutoff : recordLower - 1 + 1 = recordLower := by
    have := recordLower_gt_one
    omega
  rw [recordCutoff] at ascentUpper
  have ascentWeight :
      3 * primeWeightSumBelow recordLower < ((k - 1 : Nat) : Real) := by
    linarith [ascentUpper, ascentNumeric]
  exact recordInputs_not_isUnimodal_of_primeWeightSum_bounds k (by omega)
    recordGap_primeGap_ge twin descentDefined ascentDefined descentWeight ascentWeight

end

end PrimeFactorUnimodality
