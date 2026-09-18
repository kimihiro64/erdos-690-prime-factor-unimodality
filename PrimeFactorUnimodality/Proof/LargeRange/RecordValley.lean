import PrimeFactorUnimodality.Helpers.Unimodality.Certificate
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.RecordOrdering

set_option autoImplicit false

/-! # Converting the two record inputs into a density valley -/

namespace PrimeFactorUnimodality

noncomputable section

/-- The gap forced by the composite block occurs strictly before the record
twin-prime ascent. -/
theorem recordGapIndex_lt_recordTwinIndex :
    Nat.primeCounting' (recordGapCenter - 86399) - 1 <
      Nat.primeCounting' recordLower := by
  have lower_large : 2 < recordGapCenter - 86399 := by
    have := recordGapCenter_large
    omega
  have lower_lt_twin : recordGapCenter - 86399 < recordLower := by
    exact (Nat.sub_le recordGapCenter 86399).trans_lt recordGapCenter_lt_recordLower
  have count_pos : 0 < Nat.primeCounting' (recordGapCenter - 86399) := by
    apply Nat.pos_of_ne_zero
    rw [Nat.primeCounting', Nat.count_ne_iff_exists]
    exact ⟨2, lower_large, Nat.prime_two⟩
  have index_lt_count :
      Nat.primeCounting' (recordGapCenter - 86399) - 1 <
        Nat.primeCounting' (recordGapCenter - 86399) := by
    omega
  exact index_lt_count.trans_le
    (Nat.monotone_primeCounting' (Nat.le_of_lt lower_lt_twin))

/-- Once the two analytic ratio inequalities are supplied, the certified
4,752-gap and the later certified twin produce non-unimodality.  Keeping this
bridge independent of the expensive closed certificates lets the analytic
and computational providers compile separately. -/
theorem recordInputs_not_isUnimodal
    (k : Nat) (hk : 2 ≤ k)
    (gapBound :
      4752 ≤ primeGap (Nat.primeCounting' (recordGapCenter - 86399) - 1))
    (twin : ConsecutivePrimes recordLower recordUpper)
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (recordGapCenter - 86399) - 1)
    (ascentDefined : k - 1 ≤ Nat.primeCounting' recordLower)
    (descentRatio :
      densityRatio
          (primesBelow
            (primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1)))
          (k - 1) < 4753)
    (ascentRatio :
      3 < densityRatio (primesBelow recordLower) (k - 1)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let descentIndex := Nat.primeCounting' (recordGapCenter - 86399) - 1
  let ascentIndex := Nat.primeCounting' recordLower
  have descent_before_ascent : descentIndex < ascentIndex := by
    exact recordGapIndex_lt_recordTwinIndex
  let certificate : RatioValleyCertificate (k - 2) :=
    { descentIndex := descentIndex
      ascentIndex := ascentIndex
      ratioDefinedAtDescent := by
        simpa [show k - 2 + 1 = k - 1 by omega, descentIndex] using descentDefined
      ratioDefinedAtAscent := by
        simpa [show k - 2 + 1 = k - 1 by omega, ascentIndex] using ascentDefined
      descentBeforeAscent := descent_before_ascent
      descentRatio := by
        simpa only [show k - 2 + 1 = k - 1 by omega, descentIndex] using
          descentRatio.trans_le (by exact_mod_cast (show 4753 ≤
            primeGap (Nat.primeCounting' (recordGapCenter - 86399) - 1) + 1 by omega))
      ascentRatio := by
        rw [show k - 2 + 1 = k - 1 by omega]
        dsimp only [ascentIndex]
        rw [primeAt_primeCounting' recordLower twin.left_prime, twin.primeGap_eq,
          recordUpper_eq_lower_add_two]
        simpa using ascentRatio }
  simpa [show k - 2 + 2 = k by omega] using certificate.not_isUnimodal

end

end PrimeFactorUnimodality
