import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.RecordOrdering
import PrimeFactorUnimodality.Proof.LargeRange.RecordPrefixBounds

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Discrete side conditions for the record-input range -/

namespace PrimeFactorUnimodality

noncomputable section

private theorem record_nextPrime_le_500000
    (bounds : HasDusartPrimeCountingBounds)
    {k : Nat} (hkLower : 49 ≤ k) (hkUpper : k ≤ 38000) :
    primeAt (k - 1) ≤ 500000 := by
  have shifted := record_prefix_primeAt_le_500000 bounds
    (k := k + 1) (by omega)
  simpa [show k + 1 - 2 = k - 1 by omega] using shifted

theorem record_descentDefined
    (bounds : HasDusartPrimeCountingBounds)
    {k : Nat} (hkLower : 49 ≤ k) (hkUpper : k ≤ 38000) :
    k - 1 ≤ Nat.primeCounting' (recordGapCenter - 86399) - 1 := by
  have nextLe := record_nextPrime_le_500000 bounds hkLower hkUpper
  have cutoffLarge : 500000 < recordGapCenter - 86399 := by
    have := recordGapCenter_large
    omega
  have endpointLe : primeAt (k - 1) + 1 ≤ recordGapCenter - 86399 := by omega
  have countMono := Nat.count_monotone Nat.Prime endpointLe
  have countAt := Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime (k - 1)
  change Nat.primeCounting' (primeAt (k - 1) + 1) ≤
    Nat.primeCounting' (recordGapCenter - 86399) at countMono
  rw [Nat.primeCounting', primeAt, countAt] at countMono
  rw [Nat.sub_add_cancel (show 1 ≤ k by omega)] at countMono
  have countGe : k ≤ Nat.primeCounting' (recordGapCenter - 86399) := by
    exact countMono
  exact Nat.sub_le_sub_right countGe 1

theorem record_ascentDefined
    (bounds : HasDusartPrimeCountingBounds)
    {k : Nat} (hkLower : 49 ≤ k) (hkUpper : k ≤ 38000) :
    k - 1 ≤ Nat.primeCounting' recordLower := by
  have nextLe := record_nextPrime_le_500000 bounds hkLower hkUpper
  have cutoffLarge : 500000 < recordLower := by
    exact (show 500000 < recordGapCenter by
      have := recordGapCenter_large
      omega).trans recordGapCenter_lt_recordLower
  have endpointLe : primeAt (k - 1) + 1 ≤ recordLower := by omega
  have countMono := Nat.count_monotone Nat.Prime endpointLe
  have countAt := Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime (k - 1)
  change Nat.primeCounting' (primeAt (k - 1) + 1) ≤
    Nat.primeCounting' recordLower at countMono
  rw [Nat.primeCounting', primeAt, countAt] at countMono
  rw [Nat.sub_add_cancel (show 1 ≤ k by omega)] at countMono
  have countGe : k ≤ Nat.primeCounting' recordLower := by exact countMono
  exact (Nat.sub_le k 1).trans countGe

theorem record_prefix_le_half
    (bounds : HasDusartPrimeCountingBounds)
    {k : Nat} (hk : k ≤ 38000) :
    primeAt (k - 2) - 1 ≤ (recordGapCenter - 86399) / 2 := by
  have prefixLe := record_prefix_primeAt_le_500000 bounds
    (k := k) (by omega)
  have halfLarge : 500000 ≤ (recordGapCenter - 86399) / 2 := by
    have := recordGapCenter_large
    omega
  omega

end

end PrimeFactorUnimodality
