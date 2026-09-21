import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part010

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 001. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_001 :
    roundedReciprocalBlockSum 0 10000 = 2483060565 := by
  calc
    roundedReciprocalBlockSum 0 10000 =
        roundedReciprocalBlockSum 0 1000 +
          roundedReciprocalBlockSum 1000 2000 + roundedReciprocalBlockSum 2000 3000 + roundedReciprocalBlockSum 3000 4000 + roundedReciprocalBlockSum 4000 5000 + roundedReciprocalBlockSum 5000 6000 + roundedReciprocalBlockSum 6000 7000 + roundedReciprocalBlockSum 7000 8000 + roundedReciprocalBlockSum 8000 9000 + roundedReciprocalBlockSum 9000 10000 := by
      rw [roundedReciprocalBlockSum_add_block (show 0 ≤ 9000 by omega) (show 9000 ≤ 10000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 8000 by omega) (show 8000 ≤ 9000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 7000 by omega) (show 7000 ≤ 8000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 6000 by omega) (show 6000 ≤ 7000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 5000 by omega) (show 5000 ≤ 6000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 4000 by omega) (show 4000 ≤ 5000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 3000 by omega) (show 3000 ≤ 4000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 2000 by omega) (show 2000 ≤ 3000 by omega), roundedReciprocalBlockSum_add_block (show 0 ≤ 1000 by omega) (show 1000 ≤ 2000 by omega)]
    _ = 2198080210 + 94368436 + 51600945 + 34533709 + 26605698 + 20795475 + 18031749 + 14276023 + 12952768 + 11815552 := by
      rw [roundedReciprocalBlockSum_001, roundedReciprocalBlockSum_002, roundedReciprocalBlockSum_003, roundedReciprocalBlockSum_004, roundedReciprocalBlockSum_005, roundedReciprocalBlockSum_006, roundedReciprocalBlockSum_007, roundedReciprocalBlockSum_008, roundedReciprocalBlockSum_009, roundedReciprocalBlockSum_010]
    _ = 2483060565 := by norm_num

end PrimeFactorUnimodality
