import PrimeFactorUnimodality.Helpers.Analytic.MertensProvider
import PrimeFactorUnimodality.Proof.LargeRange.FullRecordRatioReduction

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Closed Mertens reduction for the full finite record range -/

namespace PrimeFactorUnimodality

noncomputable section

theorem fullRecordInputs_not_isUnimodal_of_closed_mertens
    (k : Nat) (hk : 4 ≤ k)
    (gapBound :
      1113106 ≤ primeGap (Nat.primeCounting' (recordGapCenter - 455703) - 1))
    (predecessorHalf :
      (recordGapCenter - 455703) / 2 <
        primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1))
    (twin : ConsecutivePrimes recordLower recordUpper)
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (recordGapCenter - 455703) - 1)
    (ascentDefined : k - 1 ≤ Nat.primeCounting' recordLower)
    (prefix_le_half :
      primeAt (k - 2) - 1 ≤ (recordGapCenter - 455703) / 2)
    (descentNumeric :
      ((k - 1 : Nat) : Real) < 1113107 *
        (Real.log (Real.log (((recordGapCenter - 455703) / 2 : Nat) : Real)) -
          Real.log (Real.log ((primeAt (k - 2) - 1 : Nat) : Real)) -
          mertensErrorConstant /
            Real.log (((recordGapCenter - 455703) / 2 : Nat) : Real) -
          mertensErrorConstant /
            Real.log ((primeAt (k - 2) - 1 : Nat) : Real)))
    (ascentNumeric :
      3 * (Real.log (Real.log ((recordLower - 1 : Nat) : Real)) + 2 / 3 +
          mertensErrorConstant / Real.log ((recordLower - 1 : Nat) : Real) + 1) <
        ((k - 1 : Nat) : Real)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let x := primeAt (k - 2) - 1
  let y := (recordGapCenter - 455703) / 2
  have x_two : 2 ≤ x := by
    have primeFive : 5 ≤ primeAt (k - 2) := by
      have indexTwo : 2 ≤ k - 2 := by omega
      have monotone := primeAt_strictMono.monotone indexTwo
      norm_num [primeAt] at monotone ⊢
      exact monotone
    dsimp only [x]
    omega
  have y_two : 2 ≤ y := by
    dsimp only [y]
    have := recordGapCenter_large
    omega
  have x_le_y : x ≤ y := by simpa only [x, y] using prefix_le_half
  have shellLower := primeWeightSumBelow_sub_lower_of_estimate_of_le
    hasMertensReciprocalPrimeEstimate x_two y_two x_le_y
  have xCutoff : x + 1 = primeAt (k - 2) := by
    dsimp only [x]
    have := one_lt_primeAt (k - 2)
    omega
  rw [xCutoff] at shellLower
  have yCutoff : y + 1 ≤
      primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1) :=
    Nat.add_one_le_iff.mpr (by simpa only [y] using predecessorHalf)
  have fullLower := primeWeightSumBelow_mono yCutoff
  have descentWeight :
      ((k - 1 : Nat) : Real) < 1113107 *
        (primeWeightSumBelow
            (primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1)) -
          primeWeightSumBelow (primeAt (k - 2))) := by
    have shellToFull :
        primeWeightSumBelow (y + 1) -
            primeWeightSumBelow (primeAt (k - 2)) ≤
          primeWeightSumBelow
              (primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1)) -
            primeWeightSumBelow (primeAt (k - 2)) := by
      linarith
    have numeric :
        ((k - 1 : Nat) : Real) < 1113107 *
          (Real.log (Real.log (y : Real)) - Real.log (Real.log (x : Real)) -
            mertensErrorConstant / Real.log (y : Real) -
            mertensErrorConstant / Real.log (x : Real)) := by
      simpa only [x, y] using descentNumeric
    nlinarith [shellLower, shellToFull]
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
  have recordCutoff : recordLower - 1 + 1 = recordLower :=
    Nat.sub_add_cancel recordLower_gt_one.le
  rw [recordCutoff] at ascentUpper
  have ascentWeight :
      3 * primeWeightSumBelow recordLower < ((k - 1 : Nat) : Real) := by
    have constantBound : Mertens.M ≤ (2 : Real) / 3 :=
      mertensConstant_lt_two_thirds.le
    nlinarith [ascentUpper]
  exact fullRecordInputs_not_isUnimodal_of_primeWeightSum_bounds k (by omega)
    gapBound twin descentDefined ascentDefined descentWeight ascentWeight

end

end PrimeFactorUnimodality
