import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group049
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part500

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 050. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_050 :
    roundedReciprocalBlockSum 490000 500000 = 1715666 := by
  calc
    roundedReciprocalBlockSum 490000 500000 =
        roundedReciprocalBlockSum 490000 491000 +
          roundedReciprocalBlockSum 491000 492000 + roundedReciprocalBlockSum 492000 493000 + roundedReciprocalBlockSum 493000 494000 + roundedReciprocalBlockSum 494000 495000 + roundedReciprocalBlockSum 495000 496000 + roundedReciprocalBlockSum 496000 497000 + roundedReciprocalBlockSum 497000 498000 + roundedReciprocalBlockSum 498000 499000 + roundedReciprocalBlockSum 499000 500000 := by
      rw [roundedReciprocalBlockSum_add_block (show 490000 ≤ 499000 by omega) (show 499000 ≤ 500000 by omega), roundedReciprocalBlockSum_add_block (show 490000 ≤ 498000 by omega) (show 498000 ≤ 499000 by omega), roundedReciprocalBlockSum_add_block (show 490000 ≤ 497000 by omega) (show 497000 ≤ 498000 by omega), roundedReciprocalBlockSum_add_block (show 490000 ≤ 496000 by omega) (show 496000 ≤ 497000 by omega), roundedReciprocalBlockSum_add_block (show 490000 ≤ 495000 by omega) (show 495000 ≤ 496000 by omega), roundedReciprocalBlockSum_add_block (show 490000 ≤ 494000 by omega) (show 494000 ≤ 495000 by omega), roundedReciprocalBlockSum_add_block (show 490000 ≤ 493000 by omega) (show 493000 ≤ 494000 by omega), roundedReciprocalBlockSum_add_block (show 490000 ≤ 492000 by omega) (show 492000 ≤ 493000 by omega), roundedReciprocalBlockSum_add_block (show 490000 ≤ 491000 by omega) (show 491000 ≤ 492000 by omega)]
    _ = 173332 + 175023 + 158417 + 176346 + 178002 + 185710 + 157138 + 184977 + 156500 + 170221 := by
      rw [roundedReciprocalBlockSum_491, roundedReciprocalBlockSum_492, roundedReciprocalBlockSum_493, roundedReciprocalBlockSum_494, roundedReciprocalBlockSum_495, roundedReciprocalBlockSum_496, roundedReciprocalBlockSum_497, roundedReciprocalBlockSum_498, roundedReciprocalBlockSum_499, roundedReciprocalBlockSum_500]
    _ = 1715666 := by norm_num

end PrimeFactorUnimodality
