import PrimeFactorUnimodality.Proof.LargeRange.ElementaryPrimePrefix
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure
import PrimeFactorUnimodality.Proof.LargeRange.RecordOrdering

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Discrete side conditions for the full finite record range -/

namespace PrimeFactorUnimodality

noncomputable section

theorem fullRecord_primeAt_le_800000000 {i : Nat} (hi : i ≤ 8600001) :
    primeAt i ≤ 800000000 := by
  have indexMono : primeAt i ≤ primeAt 8600001 :=
    primeAt_strictMono.monotone hi
  have explicit := primeAt_le_elementaryPrimeUpper
    (r := 8600001) (by norm_num)
  have valueBound : elementaryPrimeUpper 8600001 ≤ 800000000 := by
    have logValue : Nat.log 2 8600001 = 23 := by decide
    rw [elementaryPrimeUpper, tailPrimeUpper, logValue]
    norm_num
  exact indexMono.trans (explicit.trans valueBound)

theorem fullRecord_descentDefined {k : Nat}
    (hkLower : 38001 ≤ k) (hkUpper : k ≤ 8600001) :
    k - 1 ≤ Nat.primeCounting' (recordGapCenter - 455703) - 1 := by
  have nextLe : primeAt (k - 1) ≤ 800000000 :=
    fullRecord_primeAt_le_800000000 (by omega)
  have cutoffLarge : 800000000 < recordGapCenter - 455703 := by
    have := recordGapCenter_large
    omega
  have endpointLe : primeAt (k - 1) + 1 ≤ recordGapCenter - 455703 := by omega
  have countMono := Nat.count_monotone Nat.Prime endpointLe
  have countAt := Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime (k - 1)
  change Nat.primeCounting' (primeAt (k - 1) + 1) ≤
    Nat.primeCounting' (recordGapCenter - 455703) at countMono
  rw [Nat.primeCounting', primeAt, countAt] at countMono
  rw [Nat.sub_add_cancel (show 1 ≤ k by omega)] at countMono
  have countGe : k ≤ Nat.primeCounting' (recordGapCenter - 455703) := countMono
  exact Nat.sub_le_sub_right countGe 1

theorem fullRecord_ascentDefined {k : Nat}
    (hkLower : 38001 ≤ k) (hkUpper : k ≤ 8600001) :
    k - 1 ≤ Nat.primeCounting' recordLower := by
  have nextLe : primeAt (k - 1) ≤ 800000000 :=
    fullRecord_primeAt_le_800000000 (by omega)
  have cutoffLarge : 800000000 < recordLower := by
    exact (show 800000000 < recordGapCenter by
      have := recordGapCenter_large
      omega).trans recordGapCenter_lt_recordLower
  have endpointLe : primeAt (k - 1) + 1 ≤ recordLower := by omega
  have countMono := Nat.count_monotone Nat.Prime endpointLe
  have countAt := Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime (k - 1)
  change Nat.primeCounting' (primeAt (k - 1) + 1) ≤
    Nat.primeCounting' recordLower at countMono
  rw [Nat.primeCounting', primeAt, countAt] at countMono
  rw [Nat.sub_add_cancel (show 1 ≤ k by omega)] at countMono
  exact (Nat.sub_le k 1).trans countMono

theorem fullRecord_prefix_le_half {k : Nat} (hkUpper : k ≤ 8600001) :
    primeAt (k - 2) - 1 ≤ (recordGapCenter - 455703) / 2 := by
  have prefixLe : primeAt (k - 2) ≤ 800000000 :=
    fullRecord_primeAt_le_800000000 (by omega)
  have halfLarge : 800000000 ≤ (recordGapCenter - 455703) / 2 := by
    have := recordGapCenter_large
    omega
  omega

end

end PrimeFactorUnimodality
