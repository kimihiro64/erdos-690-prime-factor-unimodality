import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group047
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part480

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 048. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_048 :
    roundedReciprocalBlockSum 470000 480000 = 1794245 := by
  calc
    roundedReciprocalBlockSum 470000 480000 =
        roundedReciprocalBlockSum 470000 471000 +
          roundedReciprocalBlockSum 471000 472000 + roundedReciprocalBlockSum 472000 473000 + roundedReciprocalBlockSum 473000 474000 + roundedReciprocalBlockSum 474000 475000 + roundedReciprocalBlockSum 475000 476000 + roundedReciprocalBlockSum 476000 477000 + roundedReciprocalBlockSum 477000 478000 + roundedReciprocalBlockSum 478000 479000 + roundedReciprocalBlockSum 479000 480000 := by
      rw [roundedReciprocalBlockSum_add_block (show 470000 ≤ 479000 by omega) (show 479000 ≤ 480000 by omega), roundedReciprocalBlockSum_add_block (show 470000 ≤ 478000 by omega) (show 478000 ≤ 479000 by omega), roundedReciprocalBlockSum_add_block (show 470000 ≤ 477000 by omega) (show 477000 ≤ 478000 by omega), roundedReciprocalBlockSum_add_block (show 470000 ≤ 476000 by omega) (show 476000 ≤ 477000 by omega), roundedReciprocalBlockSum_add_block (show 470000 ≤ 475000 by omega) (show 475000 ≤ 476000 by omega), roundedReciprocalBlockSum_add_block (show 470000 ≤ 474000 by omega) (show 474000 ≤ 475000 by omega), roundedReciprocalBlockSum_add_block (show 470000 ≤ 473000 by omega) (show 473000 ≤ 474000 by omega), roundedReciprocalBlockSum_add_block (show 470000 ≤ 472000 by omega) (show 472000 ≤ 473000 by omega), roundedReciprocalBlockSum_add_block (show 470000 ≤ 471000 by omega) (show 471000 ≤ 472000 by omega)]
    _ = 189201 + 182430 + 169358 + 179544 + 187606 + 187207 + 174234 + 165481 + 196478 + 162706 := by
      rw [roundedReciprocalBlockSum_471, roundedReciprocalBlockSum_472, roundedReciprocalBlockSum_473, roundedReciprocalBlockSum_474, roundedReciprocalBlockSum_475, roundedReciprocalBlockSum_476, roundedReciprocalBlockSum_477, roundedReciprocalBlockSum_478, roundedReciprocalBlockSum_479, roundedReciprocalBlockSum_480]
    _ = 1794245 := by norm_num

end PrimeFactorUnimodality
