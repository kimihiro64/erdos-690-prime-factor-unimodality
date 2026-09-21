import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group002
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part030

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 003. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_003 :
    roundedReciprocalBlockSum 20000 30000 = 39971206 := by
  calc
    roundedReciprocalBlockSum 20000 30000 =
        roundedReciprocalBlockSum 20000 21000 +
          roundedReciprocalBlockSum 21000 22000 + roundedReciprocalBlockSum 22000 23000 + roundedReciprocalBlockSum 23000 24000 + roundedReciprocalBlockSum 24000 25000 + roundedReciprocalBlockSum 25000 26000 + roundedReciprocalBlockSum 26000 27000 + roundedReciprocalBlockSum 27000 28000 + roundedReciprocalBlockSum 28000 29000 + roundedReciprocalBlockSum 29000 30000 := by
      rw [roundedReciprocalBlockSum_add_block (show 20000 ≤ 29000 by omega) (show 29000 ≤ 30000 by omega), roundedReciprocalBlockSum_add_block (show 20000 ≤ 28000 by omega) (show 28000 ≤ 29000 by omega), roundedReciprocalBlockSum_add_block (show 20000 ≤ 27000 by omega) (show 27000 ≤ 28000 by omega), roundedReciprocalBlockSum_add_block (show 20000 ≤ 26000 by omega) (show 26000 ≤ 27000 by omega), roundedReciprocalBlockSum_add_block (show 20000 ≤ 25000 by omega) (show 25000 ≤ 26000 by omega), roundedReciprocalBlockSum_add_block (show 20000 ≤ 24000 by omega) (show 24000 ≤ 25000 by omega), roundedReciprocalBlockSum_add_block (show 20000 ≤ 23000 by omega) (show 23000 ≤ 24000 by omega), roundedReciprocalBlockSum_add_block (show 20000 ≤ 22000 by omega) (show 22000 ≤ 23000 by omega), roundedReciprocalBlockSum_add_block (show 20000 ≤ 21000 by omega) (show 21000 ≤ 22000 by omega)]
    _ = 4784842 + 4840779 + 4449409 + 4427600 + 3840776 + 3841880 + 3810152 + 3415421 + 3438340 + 3122007 := by
      rw [roundedReciprocalBlockSum_021, roundedReciprocalBlockSum_022, roundedReciprocalBlockSum_023, roundedReciprocalBlockSum_024, roundedReciprocalBlockSum_025, roundedReciprocalBlockSum_026, roundedReciprocalBlockSum_027, roundedReciprocalBlockSum_028, roundedReciprocalBlockSum_029, roundedReciprocalBlockSum_030]
    _ = 39971206 := by norm_num

end PrimeFactorUnimodality
