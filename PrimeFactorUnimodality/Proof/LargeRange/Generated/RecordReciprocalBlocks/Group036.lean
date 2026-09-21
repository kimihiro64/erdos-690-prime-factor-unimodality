import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group035
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part360

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 036. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_036 :
    roundedReciprocalBlockSum 350000 360000 = 2316436 := by
  calc
    roundedReciprocalBlockSum 350000 360000 =
        roundedReciprocalBlockSum 350000 351000 +
          roundedReciprocalBlockSum 351000 352000 + roundedReciprocalBlockSum 352000 353000 + roundedReciprocalBlockSum 353000 354000 + roundedReciprocalBlockSum 354000 355000 + roundedReciprocalBlockSum 355000 356000 + roundedReciprocalBlockSum 356000 357000 + roundedReciprocalBlockSum 357000 358000 + roundedReciprocalBlockSum 358000 359000 + roundedReciprocalBlockSum 359000 360000 := by
      rw [roundedReciprocalBlockSum_add_block (show 350000 ≤ 359000 by omega) (show 359000 ≤ 360000 by omega), roundedReciprocalBlockSum_add_block (show 350000 ≤ 358000 by omega) (show 358000 ≤ 359000 by omega), roundedReciprocalBlockSum_add_block (show 350000 ≤ 357000 by omega) (show 357000 ≤ 358000 by omega), roundedReciprocalBlockSum_add_block (show 350000 ≤ 356000 by omega) (show 356000 ≤ 357000 by omega), roundedReciprocalBlockSum_add_block (show 350000 ≤ 355000 by omega) (show 355000 ≤ 356000 by omega), roundedReciprocalBlockSum_add_block (show 350000 ≤ 354000 by omega) (show 354000 ≤ 355000 by omega), roundedReciprocalBlockSum_add_block (show 350000 ≤ 353000 by omega) (show 353000 ≤ 354000 by omega), roundedReciprocalBlockSum_add_block (show 350000 ≤ 352000 by omega) (show 352000 ≤ 353000 by omega), roundedReciprocalBlockSum_add_block (show 350000 ≤ 351000 by omega) (show 351000 ≤ 352000 by omega)]
    _ = 225422 + 250408 + 246862 + 226342 + 248297 + 230711 + 204796 + 237803 + 237115 + 208680 := by
      rw [roundedReciprocalBlockSum_351, roundedReciprocalBlockSum_352, roundedReciprocalBlockSum_353, roundedReciprocalBlockSum_354, roundedReciprocalBlockSum_355, roundedReciprocalBlockSum_356, roundedReciprocalBlockSum_357, roundedReciprocalBlockSum_358, roundedReciprocalBlockSum_359, roundedReciprocalBlockSum_360]
    _ = 2316436 := by norm_num

end PrimeFactorUnimodality
