import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group041
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part420

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 042. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_042 :
    roundedReciprocalBlockSum 410000 420000 = 2012337 := by
  calc
    roundedReciprocalBlockSum 410000 420000 =
        roundedReciprocalBlockSum 410000 411000 +
          roundedReciprocalBlockSum 411000 412000 + roundedReciprocalBlockSum 412000 413000 + roundedReciprocalBlockSum 413000 414000 + roundedReciprocalBlockSum 414000 415000 + roundedReciprocalBlockSum 415000 416000 + roundedReciprocalBlockSum 416000 417000 + roundedReciprocalBlockSum 417000 418000 + roundedReciprocalBlockSum 418000 419000 + roundedReciprocalBlockSum 419000 420000 := by
      rw [roundedReciprocalBlockSum_add_block (show 410000 ≤ 419000 by omega) (show 419000 ≤ 420000 by omega), roundedReciprocalBlockSum_add_block (show 410000 ≤ 418000 by omega) (show 418000 ≤ 419000 by omega), roundedReciprocalBlockSum_add_block (show 410000 ≤ 417000 by omega) (show 417000 ≤ 418000 by omega), roundedReciprocalBlockSum_add_block (show 410000 ≤ 416000 by omega) (show 416000 ≤ 417000 by omega), roundedReciprocalBlockSum_add_block (show 410000 ≤ 415000 by omega) (show 415000 ≤ 416000 by omega), roundedReciprocalBlockSum_add_block (show 410000 ≤ 414000 by omega) (show 414000 ≤ 415000 by omega), roundedReciprocalBlockSum_add_block (show 410000 ≤ 413000 by omega) (show 413000 ≤ 414000 by omega), roundedReciprocalBlockSum_add_block (show 410000 ≤ 412000 by omega) (show 412000 ≤ 413000 by omega), roundedReciprocalBlockSum_add_block (show 410000 ≤ 411000 by omega) (show 411000 ≤ 412000 by omega)]
    _ = 192490 + 209038 + 194005 + 179001 + 226823 + 211832 + 180122 + 206028 + 222259 + 190739 := by
      rw [roundedReciprocalBlockSum_411, roundedReciprocalBlockSum_412, roundedReciprocalBlockSum_413, roundedReciprocalBlockSum_414, roundedReciprocalBlockSum_415, roundedReciprocalBlockSum_416, roundedReciprocalBlockSum_417, roundedReciprocalBlockSum_418, roundedReciprocalBlockSum_419, roundedReciprocalBlockSum_420]
    _ = 2012337 := by norm_num

end PrimeFactorUnimodality
