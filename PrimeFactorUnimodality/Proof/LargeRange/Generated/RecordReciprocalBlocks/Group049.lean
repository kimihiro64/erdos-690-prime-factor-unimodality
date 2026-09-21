import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group048
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part490

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 049. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_049 :
    roundedReciprocalBlockSum 480000 490000 = 1703450 := by
  calc
    roundedReciprocalBlockSum 480000 490000 =
        roundedReciprocalBlockSum 480000 481000 +
          roundedReciprocalBlockSum 481000 482000 + roundedReciprocalBlockSum 482000 483000 + roundedReciprocalBlockSum 483000 484000 + roundedReciprocalBlockSum 484000 485000 + roundedReciprocalBlockSum 485000 486000 + roundedReciprocalBlockSum 486000 487000 + roundedReciprocalBlockSum 487000 488000 + roundedReciprocalBlockSum 488000 489000 + roundedReciprocalBlockSum 489000 490000 := by
      rw [roundedReciprocalBlockSum_add_block (show 480000 ≤ 489000 by omega) (show 489000 ≤ 490000 by omega), roundedReciprocalBlockSum_add_block (show 480000 ≤ 488000 by omega) (show 488000 ≤ 489000 by omega), roundedReciprocalBlockSum_add_block (show 480000 ≤ 487000 by omega) (show 487000 ≤ 488000 by omega), roundedReciprocalBlockSum_add_block (show 480000 ≤ 486000 by omega) (show 486000 ≤ 487000 by omega), roundedReciprocalBlockSum_add_block (show 480000 ≤ 485000 by omega) (show 485000 ≤ 486000 by omega), roundedReciprocalBlockSum_add_block (show 480000 ≤ 484000 by omega) (show 484000 ≤ 485000 by omega), roundedReciprocalBlockSum_add_block (show 480000 ≤ 483000 by omega) (show 483000 ≤ 484000 by omega), roundedReciprocalBlockSum_add_block (show 480000 ≤ 482000 by omega) (show 482000 ≤ 483000 by omega), roundedReciprocalBlockSum_add_block (show 480000 ≤ 481000 by omega) (show 481000 ≤ 482000 by omega)]
    _ = 174871 + 168275 + 180349 + 167567 + 146599 + 154525 + 180927 + 174405 + 184294 + 171638 := by
      rw [roundedReciprocalBlockSum_481, roundedReciprocalBlockSum_482, roundedReciprocalBlockSum_483, roundedReciprocalBlockSum_484, roundedReciprocalBlockSum_485, roundedReciprocalBlockSum_486, roundedReciprocalBlockSum_487, roundedReciprocalBlockSum_488, roundedReciprocalBlockSum_489, roundedReciprocalBlockSum_490]
    _ = 1703450 := by norm_num

end PrimeFactorUnimodality
