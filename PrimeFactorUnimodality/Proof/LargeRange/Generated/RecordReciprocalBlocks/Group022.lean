import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group021
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part220

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 022. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_022 :
    roundedReciprocalBlockSum 210000 220000 = 3772281 := by
  calc
    roundedReciprocalBlockSum 210000 220000 =
        roundedReciprocalBlockSum 210000 211000 +
          roundedReciprocalBlockSum 211000 212000 + roundedReciprocalBlockSum 212000 213000 + roundedReciprocalBlockSum 213000 214000 + roundedReciprocalBlockSum 214000 215000 + roundedReciprocalBlockSum 215000 216000 + roundedReciprocalBlockSum 216000 217000 + roundedReciprocalBlockSum 217000 218000 + roundedReciprocalBlockSum 218000 219000 + roundedReciprocalBlockSum 219000 220000 := by
      rw [roundedReciprocalBlockSum_add_block (show 210000 ≤ 219000 by omega) (show 219000 ≤ 220000 by omega), roundedReciprocalBlockSum_add_block (show 210000 ≤ 218000 by omega) (show 218000 ≤ 219000 by omega), roundedReciprocalBlockSum_add_block (show 210000 ≤ 217000 by omega) (show 217000 ≤ 218000 by omega), roundedReciprocalBlockSum_add_block (show 210000 ≤ 216000 by omega) (show 216000 ≤ 217000 by omega), roundedReciprocalBlockSum_add_block (show 210000 ≤ 215000 by omega) (show 215000 ≤ 216000 by omega), roundedReciprocalBlockSum_add_block (show 210000 ≤ 214000 by omega) (show 214000 ≤ 215000 by omega), roundedReciprocalBlockSum_add_block (show 210000 ≤ 213000 by omega) (show 213000 ≤ 214000 by omega), roundedReciprocalBlockSum_add_block (show 210000 ≤ 212000 by omega) (show 212000 ≤ 213000 by omega), roundedReciprocalBlockSum_add_block (show 210000 ≤ 211000 by omega) (show 211000 ≤ 212000 by omega)]
    _ = 399144 + 406660 + 324704 + 379451 + 400997 + 343383 + 351045 + 367894 + 384447 + 414556 := by
      rw [roundedReciprocalBlockSum_211, roundedReciprocalBlockSum_212, roundedReciprocalBlockSum_213, roundedReciprocalBlockSum_214, roundedReciprocalBlockSum_215, roundedReciprocalBlockSum_216, roundedReciprocalBlockSum_217, roundedReciprocalBlockSum_218, roundedReciprocalBlockSum_219, roundedReciprocalBlockSum_220]
    _ = 3772281 := by norm_num

end PrimeFactorUnimodality
