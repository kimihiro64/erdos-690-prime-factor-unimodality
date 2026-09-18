import Mathlib.NumberTheory.Bertrand
import PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure

set_option autoImplicit false

/-! # Consequences of the full published record-gap block

The historical endpoint primality certificates are unnecessary here. A
certificate for every interior integer alone forces an indexed prime gap of
the published length, and Bertrand supplies a sufficiently large predecessor.
-/

namespace PrimeFactorUnimodality

theorem fullRecordGap_primeGap_ge_of_blocks
    (subBlock : ∀ d, d ≤ 455703 → ¬(recordGapCenter - d).Prime)
    (addBlock : ∀ d, d ≤ 657401 → ¬(recordGapCenter + d).Prime) :
    1113106 ≤ primeGap (Nat.primeCounting' (recordGapCenter - 455703) - 1) := by
  have center_large : 8_000_000_000 < recordGapCenter := recordGapCenter_large
  have interval_gap := primeGap_ge_of_not_prime_Icc
    (lower := recordGapCenter - 455703) (upper := recordGapCenter + 657401)
    (by omega) (by omega) (fun n lower upper => by
      by_cases n_le_center : n ≤ recordGapCenter
      · let d := recordGapCenter - n
        have d_upper : d ≤ 455703 := by
          dsimp only [d]
          omega
        simpa only [d, Nat.sub_sub_self n_le_center] using subBlock d d_upper
      · let d := n - recordGapCenter
        have d_upper : d ≤ 657401 := by
          dsimp only [d]
          omega
        have center_add : recordGapCenter + d = n := by
          dsimp only [d]
          omega
        simpa only [center_add] using addBlock d d_upper)
  have interval_length :
      (recordGapCenter + 657401) - (recordGapCenter - 455703) + 2 = 1113106 := by
    omega
  rwa [interval_length] at interval_gap

theorem fullRecordGap_predecessor_gt_half_of_subBlock
    (subBlock : ∀ d, d ≤ 455703 → ¬(recordGapCenter - d).Prime) :
    (recordGapCenter - 455703) / 2 <
      primeAt (Nat.primeCounting' (recordGapCenter - 455703) - 1) := by
  let lower := recordGapCenter - 455703
  let half := lower / 2
  have lower_large : 512 ≤ lower := by
    dsimp only [lower]
    have := recordGapCenter_large
    omega
  have half_ne_zero : half ≠ 0 := by
    dsimp only [half]
    omega
  rcases Nat.exists_prime_lt_and_le_two_mul half half_ne_zero with
    ⟨p, p_prime, half_lt_p, p_le⟩
  have lower_not_prime : ¬lower.Prime := by
    dsimp only [lower]
    simpa using subBlock 455703 (by norm_num)
  have p_lt_lower : p < lower := by
    have two_half_le : 2 * half ≤ lower := by
      dsimp only [half]
      omega
    have p_le_lower : p ≤ lower := p_le.trans two_half_le
    exact p_le_lower.lt_of_ne (fun p_eq ↦ lower_not_prime (p_eq ▸ p_prime))
  exact half_lt_p.trans_le
    (prime_le_primeAt_primeCounting'_sub_one p_prime p_lt_lower)

end PrimeFactorUnimodality
