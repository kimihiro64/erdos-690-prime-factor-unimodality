import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group004
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part050

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 005. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_005 :
    roundedReciprocalBlockSum 40000 50000 = 20757282 := by
  calc
    roundedReciprocalBlockSum 40000 50000 =
        roundedReciprocalBlockSum 40000 41000 +
          roundedReciprocalBlockSum 41000 42000 + roundedReciprocalBlockSum 42000 43000 + roundedReciprocalBlockSum 43000 44000 + roundedReciprocalBlockSum 44000 45000 + roundedReciprocalBlockSum 45000 46000 + roundedReciprocalBlockSum 46000 47000 + roundedReciprocalBlockSum 47000 48000 + roundedReciprocalBlockSum 48000 49000 + roundedReciprocalBlockSum 49000 50000 := by
      rw [roundedReciprocalBlockSum_add_block (show 40000 ≤ 49000 by omega) (show 49000 ≤ 50000 by omega), roundedReciprocalBlockSum_add_block (show 40000 ≤ 48000 by omega) (show 48000 ≤ 49000 by omega), roundedReciprocalBlockSum_add_block (show 40000 ≤ 47000 by omega) (show 47000 ≤ 48000 by omega), roundedReciprocalBlockSum_add_block (show 40000 ≤ 46000 by omega) (show 46000 ≤ 47000 by omega), roundedReciprocalBlockSum_add_block (show 40000 ≤ 45000 by omega) (show 45000 ≤ 46000 by omega), roundedReciprocalBlockSum_add_block (show 40000 ≤ 44000 by omega) (show 44000 ≤ 45000 by omega), roundedReciprocalBlockSum_add_block (show 40000 ≤ 43000 by omega) (show 43000 ≤ 44000 by omega), roundedReciprocalBlockSum_add_block (show 40000 ≤ 42000 by omega) (show 42000 ≤ 43000 by omega), roundedReciprocalBlockSum_add_block (show 40000 ≤ 41000 by omega) (show 41000 ≤ 42000 by omega)]
    _ = 2172645 + 2433522 + 2400246 + 1953306 + 2157427 + 1889900 + 1935763 + 1999484 + 1834692 + 1980297 := by
      rw [roundedReciprocalBlockSum_041, roundedReciprocalBlockSum_042, roundedReciprocalBlockSum_043, roundedReciprocalBlockSum_044, roundedReciprocalBlockSum_045, roundedReciprocalBlockSum_046, roundedReciprocalBlockSum_047, roundedReciprocalBlockSum_048, roundedReciprocalBlockSum_049, roundedReciprocalBlockSum_050]
    _ = 20757282 := by norm_num

end PrimeFactorUnimodality
