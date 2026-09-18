import Mathlib.NumberTheory.Bertrand
import PrimeFactorUnimodality.Helpers.PrimeSequence.Consecutive
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure

set_option autoImplicit false

/-! # Prime-gap consequence of the certified composite block -/

namespace PrimeFactorUnimodality

/-- The complete offset certificate implies an indexed prime gap of at least
`4,752`.  This implication does not require primality certificates for the
historical record gap's published endpoints. -/
theorem recordGap_primeGap_ge_of_block
    (block : ∀ d, 81649 ≤ d → d ≤ 86399 → ¬(recordGapCenter - d).Prime) :
    4752 ≤ primeGap (Nat.primeCounting' (recordGapCenter - 86399) - 1) := by
  have center_large : 8_000_000_000 < recordGapCenter := recordGapCenter_large
  have interval_gap := primeGap_ge_of_not_prime_Icc
    (lower := recordGapCenter - 86399) (upper := recordGapCenter - 81649)
    (by omega) (by omega) (fun n lower upper => by
      have n_le_center : n ≤ recordGapCenter := by omega
      let d := recordGapCenter - n
      have d_lower : 81649 ≤ d := by
        dsimp only [d]
        omega
      have d_upper : d ≤ 86399 := by
        dsimp only [d]
        omega
      simpa only [d, Nat.sub_sub_self n_le_center] using block d d_lower d_upper)
  have interval_length :
      (recordGapCenter - 81649) - (recordGapCenter - 86399) + 2 = 4752 := by
    omega
  rwa [interval_length] at interval_gap

/-- A certified block also puts its predecessor prime beyond half the block's
location, by Bertrand's postulate. -/
theorem recordGap_predecessor_gt_half_of_block
    (block : ∀ d, 81649 ≤ d → d ≤ 86399 → ¬(recordGapCenter - d).Prime) :
    (recordGapCenter - 86399) / 2 <
      primeAt (Nat.primeCounting' (recordGapCenter - 86399) - 1) := by
  let lower := recordGapCenter - 86399
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
    simpa using block 86399 (by norm_num) (by norm_num)
  have p_lt_lower : p < lower := by
    have two_half_le : 2 * half ≤ lower := by
      dsimp only [half]
      omega
    have p_le_lower : p ≤ lower := p_le.trans two_half_le
    exact p_le_lower.lt_of_ne (fun p_eq => lower_not_prime (p_eq ▸ p_prime))
  exact half_lt_p.trans_le
    (prime_le_primeAt_primeCounting'_sub_one p_prime p_lt_lower)

end PrimeFactorUnimodality
