import PrimeFactorUnimodality.Helpers.Unimodality.Certificate
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.RecordOrdering

set_option autoImplicit false

/-! # Density valley from the full record gap and record twin -/

namespace PrimeFactorUnimodality

noncomputable section

theorem fullRecordGapIndex_lt_recordTwinIndex :
    Nat.primeCounting' (recordGapCenter - 455703) - 1 <
      Nat.primeCounting' recordLower := by
  have lower_large : 2 < recordGapCenter - 455703 := by
    have := recordGapCenter_large
    omega
  have lower_lt_twin : recordGapCenter - 455703 < recordLower :=
    (Nat.sub_le recordGapCenter 455703).trans_lt recordGapCenter_lt_recordLower
  have count_pos : 0 < Nat.primeCounting' (recordGapCenter - 455703) := by
    apply Nat.pos_of_ne_zero
    rw [Nat.primeCounting', Nat.count_ne_iff_exists]
    exact ⟨2, lower_large, Nat.prime_two⟩
  have index_lt_count :
      Nat.primeCounting' (recordGapCenter - 455703) - 1 <
        Nat.primeCounting' (recordGapCenter - 455703) := by
    omega
  exact index_lt_count.trans_le
    (Nat.monotone_primeCounting' lower_lt_twin.le)

theorem fullRecordInputs_not_isUnimodal
    (k : Nat) (hk : 2 ≤ k)
    (gapBound :
      1113106 ≤ primeGap (Nat.primeCounting' (recordGapCenter - 455703) - 1))
    (twin : ConsecutivePrimes recordLower recordUpper)
    (descentDefined :
      k - 1 ≤ Nat.primeCounting' (recordGapCenter - 455703) - 1)
    (ascentDefined : k - 1 ≤ Nat.primeCounting' recordLower)
    (descentRatio :
      densityRatio
          (primesBelow
            (primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1)))
          (k - 1) < 1113107)
    (ascentRatio :
      3 < densityRatio (primesBelow recordLower) (k - 1)) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  let descentIndex := Nat.primeCounting' (recordGapCenter - 455703) - 1
  let ascentIndex := Nat.primeCounting' recordLower
  let certificate : RatioValleyCertificate (k - 2) :=
    { descentIndex := descentIndex
      ascentIndex := ascentIndex
      ratioDefinedAtDescent := by
        simpa [show k - 2 + 1 = k - 1 by omega, descentIndex] using descentDefined
      ratioDefinedAtAscent := by
        simpa [show k - 2 + 1 = k - 1 by omega, ascentIndex] using ascentDefined
      descentBeforeAscent := fullRecordGapIndex_lt_recordTwinIndex
      descentRatio := by
        simpa only [show k - 2 + 1 = k - 1 by omega, descentIndex] using
          descentRatio.trans_le (by exact_mod_cast (show 1113107 ≤
            primeGap (Nat.primeCounting' (recordGapCenter - 455703) - 1) + 1 by
              omega))
      ascentRatio := by
        rw [show k - 2 + 1 = k - 1 by omega]
        dsimp only [ascentIndex]
        rw [primeAt_primeCounting' recordLower twin.left_prime, twin.primeGap_eq,
          recordUpper_eq_lower_add_two]
        simpa using ascentRatio }
  simpa [show k - 2 + 2 = k by omega] using certificate.not_isUnimodal

end

end PrimeFactorUnimodality
