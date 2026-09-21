import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group012
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part130

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 013. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_013 :
    roundedReciprocalBlockSum 120000 130000 = 6869707 := by
  calc
    roundedReciprocalBlockSum 120000 130000 =
        roundedReciprocalBlockSum 120000 121000 +
          roundedReciprocalBlockSum 121000 122000 + roundedReciprocalBlockSum 122000 123000 + roundedReciprocalBlockSum 123000 124000 + roundedReciprocalBlockSum 124000 125000 + roundedReciprocalBlockSum 125000 126000 + roundedReciprocalBlockSum 126000 127000 + roundedReciprocalBlockSum 127000 128000 + roundedReciprocalBlockSum 128000 129000 + roundedReciprocalBlockSum 129000 130000 := by
      rw [roundedReciprocalBlockSum_add_block (show 120000 ≤ 129000 by omega) (show 129000 ≤ 130000 by omega), roundedReciprocalBlockSum_add_block (show 120000 ≤ 128000 by omega) (show 128000 ≤ 129000 by omega), roundedReciprocalBlockSum_add_block (show 120000 ≤ 127000 by omega) (show 127000 ≤ 128000 by omega), roundedReciprocalBlockSum_add_block (show 120000 ≤ 126000 by omega) (show 126000 ≤ 127000 by omega), roundedReciprocalBlockSum_add_block (show 120000 ≤ 125000 by omega) (show 125000 ≤ 126000 by omega), roundedReciprocalBlockSum_add_block (show 120000 ≤ 124000 by omega) (show 124000 ≤ 125000 by omega), roundedReciprocalBlockSum_add_block (show 120000 ≤ 123000 by omega) (show 123000 ≤ 124000 by omega), roundedReciprocalBlockSum_add_block (show 120000 ≤ 122000 by omega) (show 122000 ≤ 123000 by omega), roundedReciprocalBlockSum_add_block (show 120000 ≤ 121000 by omega) (show 121000 ≤ 122000 by omega)]
    _ = 730172 + 707963 + 718567 + 712522 + 666663 + 669408 + 656357 + 674451 + 692531 + 641073 := by
      rw [roundedReciprocalBlockSum_121, roundedReciprocalBlockSum_122, roundedReciprocalBlockSum_123, roundedReciprocalBlockSum_124, roundedReciprocalBlockSum_125, roundedReciprocalBlockSum_126, roundedReciprocalBlockSum_127, roundedReciprocalBlockSum_128, roundedReciprocalBlockSum_129, roundedReciprocalBlockSum_130]
    _ = 6869707 := by norm_num

end PrimeFactorUnimodality
