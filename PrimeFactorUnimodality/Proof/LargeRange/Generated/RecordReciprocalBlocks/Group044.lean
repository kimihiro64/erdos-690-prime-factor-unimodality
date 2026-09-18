import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part431
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part432
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part433
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part434
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part435
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part436
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part437
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part438
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part439
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part440

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 044. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_044 :
    roundedReciprocalBlockSum 430000 440000 = 1945710 := by
  calc
    roundedReciprocalBlockSum 430000 440000 =
        roundedReciprocalBlockSum 430000 431000 +
          roundedReciprocalBlockSum 431000 432000 + roundedReciprocalBlockSum 432000 433000 + roundedReciprocalBlockSum 433000 434000 + roundedReciprocalBlockSum 434000 435000 + roundedReciprocalBlockSum 435000 436000 + roundedReciprocalBlockSum 436000 437000 + roundedReciprocalBlockSum 437000 438000 + roundedReciprocalBlockSum 438000 439000 + roundedReciprocalBlockSum 439000 440000 := by
      rw [roundedReciprocalBlockSum_add_block (show 430000 ≤ 439000 by omega) (show 439000 ≤ 440000 by omega), roundedReciprocalBlockSum_add_block (show 430000 ≤ 438000 by omega) (show 438000 ≤ 439000 by omega), roundedReciprocalBlockSum_add_block (show 430000 ≤ 437000 by omega) (show 437000 ≤ 438000 by omega), roundedReciprocalBlockSum_add_block (show 430000 ≤ 436000 by omega) (show 436000 ≤ 437000 by omega), roundedReciprocalBlockSum_add_block (show 430000 ≤ 435000 by omega) (show 435000 ≤ 436000 by omega), roundedReciprocalBlockSum_add_block (show 430000 ≤ 434000 by omega) (show 434000 ≤ 435000 by omega), roundedReciprocalBlockSum_add_block (show 430000 ≤ 433000 by omega) (show 433000 ≤ 434000 by omega), roundedReciprocalBlockSum_add_block (show 430000 ≤ 432000 by omega) (show 432000 ≤ 433000 by omega), roundedReciprocalBlockSum_add_block (show 430000 ≤ 431000 by omega) (show 431000 ≤ 432000 by omega)]
    _ = 199783 + 197031 + 210464 + 198439 + 209473 + 202101 + 183314 + 173753 + 184748 + 186604 := by
      rw [roundedReciprocalBlockSum_431, roundedReciprocalBlockSum_432, roundedReciprocalBlockSum_433, roundedReciprocalBlockSum_434, roundedReciprocalBlockSum_435, roundedReciprocalBlockSum_436, roundedReciprocalBlockSum_437, roundedReciprocalBlockSum_438, roundedReciprocalBlockSum_439, roundedReciprocalBlockSum_440]
    _ = 1945710 := by norm_num

end PrimeFactorUnimodality
