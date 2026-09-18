import PrimeFactorUnimodality.Helpers.Analytic.MertensProvider
import PrimeFactorUnimodality.Proof.LargeRange.RecordAnalyticReduction

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Large-range reductions with the proved Mertens input closed -/

namespace PrimeFactorUnimodality

noncomputable section

/-- Record-input reduction with the reciprocal-prime theorem and the upper
bound for its constant discharged internally. -/
theorem recordInputs_not_isUnimodal_of_closed_mertens
    (k : Nat) (hk : 4 ≤ k)
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
          mertensErrorConstant /
            Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real) -
          mertensErrorConstant /
            Real.log ((primeAt (k - 2) - 1 : Nat) : Real)))
    (ascentNumeric :
      3 * (Real.log (Real.log ((recordLower - 1 : Nat) : Real)) + 2 / 3 +
          mertensErrorConstant / Real.log ((recordLower - 1 : Nat) : Real) + 1) <
        ((k - 1 : Nat) : Real)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  apply recordInputs_not_isUnimodal_of_mertens_bounds k hk
    hasMertensReciprocalPrimeEstimate twin descentDefined ascentDefined
    prefix_le_half descentNumeric
  calc
    3 * (Real.log (Real.log ((recordLower - 1 : Nat) : Real)) + Mertens.M +
          mertensErrorConstant / Real.log ((recordLower - 1 : Nat) : Real) + 1) ≤
        3 * (Real.log (Real.log ((recordLower - 1 : Nat) : Real)) + 2 / 3 +
          mertensErrorConstant / Real.log ((recordLower - 1 : Nat) : Real) + 1) := by
      gcongr
      exact mertensConstant_lt_two_thirds.le
    _ < ((k - 1 : Nat) : Real) := ascentNumeric

/-- Record-input reduction in which a finite certificate controls the lower
endpoint of the descent shell. -/
theorem recordInputs_not_isUnimodal_of_finite_prefix
    (k : Nat) (hk : 4 ≤ k) (prefixBound : Real)
    (twin : ConsecutivePrimes recordLower recordUpper)
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (recordGapCenter - 86399) - 1)
    (ascentDefined : k - 1 ≤ Nat.primeCounting' recordLower)
    (prefix_le_half :
      primeAt (k - 2) - 1 ≤ (recordGapCenter - 86399) / 2)
    (prefixReciprocalUpper :
      reciprocalPrimeSumBelow (primeAt (k - 2)) ≤ prefixBound)
    (descentNumeric :
      ((k - 1 : Nat) : Real) < 4753 *
        (Real.log (Real.log
            (((recordGapCenter - 86399) / 2 : Nat) : Real)) +
          Mertens.M - mertensErrorConstant /
            Real.log (((recordGapCenter - 86399) / 2 : Nat) : Real) -
          prefixBound))
    (ascentNumeric :
      3 * (Real.log (Real.log ((recordLower - 1 : Nat) : Real)) + 2 / 3 +
          mertensErrorConstant / Real.log ((recordLower - 1 : Nat) : Real) + 1) <
        ((k - 1 : Nat) : Real)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let y := (recordGapCenter - 86399) / 2
  have yTwo : 2 ≤ y := by
    dsimp only [y]
    have := recordGapCenter_large
    omega
  have prefixLeY : primeAt (k - 2) ≤ y + 1 := by
    dsimp only [y]
    have primePositive := one_lt_primeAt (k - 2)
    omega
  have reciprocalLower := reciprocalPrimeSumBelow_lower_of_estimate
    hasMertensReciprocalPrimeEstimate yTwo
  have shellLower :
      Real.log (Real.log (y : Real)) + Mertens.M -
          mertensErrorConstant / Real.log (y : Real) - prefixBound ≤
        primeWeightSumBelow (y + 1) -
          primeWeightSumBelow (primeAt (k - 2)) := by
    have reciprocalShell :
        Real.log (Real.log (y : Real)) + Mertens.M -
            mertensErrorConstant / Real.log (y : Real) - prefixBound ≤
          reciprocalPrimeSumBelow (y + 1) -
            reciprocalPrimeSumBelow (primeAt (k - 2)) := by
      linarith
    exact reciprocalShell.trans
      (reciprocal_sub_le_primeWeight_sub prefixLeY)
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
        primeWeightSumBelow (y + 1) - primeWeightSumBelow (primeAt (k - 2)) ≤
          primeWeightSumBelow
              (primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1)) -
            primeWeightSumBelow (primeAt (k - 2)) := by
      linarith
    have numeric :
        ((k - 1 : Nat) : Real) < 4753 *
          (Real.log (Real.log (y : Real)) + Mertens.M -
            mertensErrorConstant / Real.log (y : Real) - prefixBound) := by
      simpa only [y] using descentNumeric
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
    hasMertensReciprocalPrimeEstimate recordPredTwo
  have recordCutoff : recordLower - 1 + 1 = recordLower := by
    exact Nat.sub_add_cancel recordLower_gt_one.le
  rw [recordCutoff] at ascentUpper
  have ascentWeight :
      3 * primeWeightSumBelow recordLower < ((k - 1 : Nat) : Real) := by
    have constantBound : Mertens.M ≤ (2 : Real) / 3 :=
      mertensConstant_lt_two_thirds.le
    linarith [ascentUpper]
  exact recordInputs_not_isUnimodal_of_primeWeightSum_bounds k (by omega)
    recordGap_primeGap_ge twin descentDefined ascentDefined descentWeight ascentWeight

end

end PrimeFactorUnimodality
