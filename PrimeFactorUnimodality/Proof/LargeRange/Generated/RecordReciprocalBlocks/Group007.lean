import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group006
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part070

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 007. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_007 :
    roundedReciprocalBlockSum 60000 70000 = 13541006 := by
  calc
    roundedReciprocalBlockSum 60000 70000 =
        roundedReciprocalBlockSum 60000 61000 +
          roundedReciprocalBlockSum 61000 62000 + roundedReciprocalBlockSum 62000 63000 + roundedReciprocalBlockSum 63000 64000 + roundedReciprocalBlockSum 64000 65000 + roundedReciprocalBlockSum 65000 66000 + roundedReciprocalBlockSum 66000 67000 + roundedReciprocalBlockSum 67000 68000 + roundedReciprocalBlockSum 68000 69000 + roundedReciprocalBlockSum 69000 70000 := by
      rw [roundedReciprocalBlockSum_add_block (show 60000 ≤ 69000 by omega) (show 69000 ≤ 70000 by omega), roundedReciprocalBlockSum_add_block (show 60000 ≤ 68000 by omega) (show 68000 ≤ 69000 by omega), roundedReciprocalBlockSum_add_block (show 60000 ≤ 67000 by omega) (show 67000 ≤ 68000 by omega), roundedReciprocalBlockSum_add_block (show 60000 ≤ 66000 by omega) (show 66000 ≤ 67000 by omega), roundedReciprocalBlockSum_add_block (show 60000 ≤ 65000 by omega) (show 65000 ≤ 66000 by omega), roundedReciprocalBlockSum_add_block (show 60000 ≤ 64000 by omega) (show 64000 ≤ 65000 by omega), roundedReciprocalBlockSum_add_block (show 60000 ≤ 63000 by omega) (show 63000 ≤ 64000 by omega), roundedReciprocalBlockSum_add_block (show 60000 ≤ 62000 by omega) (show 62000 ≤ 63000 by omega), roundedReciprocalBlockSum_add_block (show 60000 ≤ 61000 by omega) (show 61000 ≤ 62000 by omega)]
    _ = 1454689 + 1414412 + 1408016 + 1464327 + 1240399 + 1496343 + 1262827 + 1466596 + 1167573 + 1165824 := by
      rw [roundedReciprocalBlockSum_061, roundedReciprocalBlockSum_062, roundedReciprocalBlockSum_063, roundedReciprocalBlockSum_064, roundedReciprocalBlockSum_065, roundedReciprocalBlockSum_066, roundedReciprocalBlockSum_067, roundedReciprocalBlockSum_068, roundedReciprocalBlockSum_069, roundedReciprocalBlockSum_070]
    _ = 13541006 := by norm_num

end PrimeFactorUnimodality
