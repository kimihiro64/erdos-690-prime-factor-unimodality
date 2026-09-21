import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group044
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part450

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 045. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_045 :
    roundedReciprocalBlockSum 440000 450000 = 1861399 := by
  calc
    roundedReciprocalBlockSum 440000 450000 =
        roundedReciprocalBlockSum 440000 441000 +
          roundedReciprocalBlockSum 441000 442000 + roundedReciprocalBlockSum 442000 443000 + roundedReciprocalBlockSum 443000 444000 + roundedReciprocalBlockSum 444000 445000 + roundedReciprocalBlockSum 445000 446000 + roundedReciprocalBlockSum 446000 447000 + roundedReciprocalBlockSum 447000 448000 + roundedReciprocalBlockSum 448000 449000 + roundedReciprocalBlockSum 449000 450000 := by
      rw [roundedReciprocalBlockSum_add_block (show 440000 ≤ 449000 by omega) (show 449000 ≤ 450000 by omega), roundedReciprocalBlockSum_add_block (show 440000 ≤ 448000 by omega) (show 448000 ≤ 449000 by omega), roundedReciprocalBlockSum_add_block (show 440000 ≤ 447000 by omega) (show 447000 ≤ 448000 by omega), roundedReciprocalBlockSum_add_block (show 440000 ≤ 446000 by omega) (show 446000 ≤ 447000 by omega), roundedReciprocalBlockSum_add_block (show 440000 ≤ 445000 by omega) (show 445000 ≤ 446000 by omega), roundedReciprocalBlockSum_add_block (show 440000 ≤ 444000 by omega) (show 444000 ≤ 445000 by omega), roundedReciprocalBlockSum_add_block (show 440000 ≤ 443000 by omega) (show 443000 ≤ 444000 by omega), roundedReciprocalBlockSum_add_block (show 440000 ≤ 442000 by omega) (show 442000 ≤ 443000 by omega), roundedReciprocalBlockSum_add_block (show 440000 ≤ 441000 by omega) (show 441000 ≤ 442000 by omega)]
    _ = 188454 + 172188 + 203438 + 214258 + 202520 + 166147 + 170264 + 176581 + 171724 + 195825 := by
      rw [roundedReciprocalBlockSum_441, roundedReciprocalBlockSum_442, roundedReciprocalBlockSum_443, roundedReciprocalBlockSum_444, roundedReciprocalBlockSum_445, roundedReciprocalBlockSum_446, roundedReciprocalBlockSum_447, roundedReciprocalBlockSum_448, roundedReciprocalBlockSum_449, roundedReciprocalBlockSum_450]
    _ = 1861399 := by norm_num

end PrimeFactorUnimodality
