import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group003
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part040

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 004. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_004 :
    roundedReciprocalBlockSum 30000 40000 = 27589049 := by
  calc
    roundedReciprocalBlockSum 30000 40000 =
        roundedReciprocalBlockSum 30000 31000 +
          roundedReciprocalBlockSum 31000 32000 + roundedReciprocalBlockSum 32000 33000 + roundedReciprocalBlockSum 33000 34000 + roundedReciprocalBlockSum 34000 35000 + roundedReciprocalBlockSum 35000 36000 + roundedReciprocalBlockSum 36000 37000 + roundedReciprocalBlockSum 37000 38000 + roundedReciprocalBlockSum 38000 39000 + roundedReciprocalBlockSum 39000 40000 := by
      rw [roundedReciprocalBlockSum_add_block (show 30000 ≤ 39000 by omega) (show 39000 ≤ 40000 by omega), roundedReciprocalBlockSum_add_block (show 30000 ≤ 38000 by omega) (show 38000 ≤ 39000 by omega), roundedReciprocalBlockSum_add_block (show 30000 ≤ 37000 by omega) (show 37000 ≤ 38000 by omega), roundedReciprocalBlockSum_add_block (show 30000 ≤ 36000 by omega) (show 36000 ≤ 37000 by omega), roundedReciprocalBlockSum_add_block (show 30000 ≤ 35000 by omega) (show 35000 ≤ 36000 by omega), roundedReciprocalBlockSum_add_block (show 30000 ≤ 34000 by omega) (show 34000 ≤ 35000 by omega), roundedReciprocalBlockSum_add_block (show 30000 ≤ 33000 by omega) (show 33000 ≤ 34000 by omega), roundedReciprocalBlockSum_add_block (show 30000 ≤ 32000 by omega) (show 32000 ≤ 33000 by omega), roundedReciprocalBlockSum_add_block (show 30000 ≤ 31000 by omega) (show 31000 ≤ 32000 by omega)]
    _ = 3115484 + 2924352 + 3262605 + 2985118 + 2724787 + 2591812 + 2711133 + 2506798 + 2336259 + 2430701 := by
      rw [roundedReciprocalBlockSum_031, roundedReciprocalBlockSum_032, roundedReciprocalBlockSum_033, roundedReciprocalBlockSum_034, roundedReciprocalBlockSum_035, roundedReciprocalBlockSum_036, roundedReciprocalBlockSum_037, roundedReciprocalBlockSum_038, roundedReciprocalBlockSum_039, roundedReciprocalBlockSum_040]
    _ = 27589049 := by norm_num

end PrimeFactorUnimodality
