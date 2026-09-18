import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part171
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part172
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part173
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part174
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part175
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part176
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part177
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part178
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part179
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part180

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 018. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_018 :
    roundedReciprocalBlockSum 170000 180000 = 4828892 := by
  calc
    roundedReciprocalBlockSum 170000 180000 =
        roundedReciprocalBlockSum 170000 171000 +
          roundedReciprocalBlockSum 171000 172000 + roundedReciprocalBlockSum 172000 173000 + roundedReciprocalBlockSum 173000 174000 + roundedReciprocalBlockSum 174000 175000 + roundedReciprocalBlockSum 175000 176000 + roundedReciprocalBlockSum 176000 177000 + roundedReciprocalBlockSum 177000 178000 + roundedReciprocalBlockSum 178000 179000 + roundedReciprocalBlockSum 179000 180000 := by
      rw [roundedReciprocalBlockSum_add_block (show 170000 ≤ 179000 by omega) (show 179000 ≤ 180000 by omega), roundedReciprocalBlockSum_add_block (show 170000 ≤ 178000 by omega) (show 178000 ≤ 179000 by omega), roundedReciprocalBlockSum_add_block (show 170000 ≤ 177000 by omega) (show 177000 ≤ 178000 by omega), roundedReciprocalBlockSum_add_block (show 170000 ≤ 176000 by omega) (show 176000 ≤ 177000 by omega), roundedReciprocalBlockSum_add_block (show 170000 ≤ 175000 by omega) (show 175000 ≤ 176000 by omega), roundedReciprocalBlockSum_add_block (show 170000 ≤ 174000 by omega) (show 174000 ≤ 175000 by omega), roundedReciprocalBlockSum_add_block (show 170000 ≤ 173000 by omega) (show 173000 ≤ 174000 by omega), roundedReciprocalBlockSum_add_block (show 170000 ≤ 172000 by omega) (show 172000 ≤ 173000 by omega), roundedReciprocalBlockSum_add_block (show 170000 ≤ 171000 by omega) (show 171000 ≤ 172000 by omega)]
    _ = 510340 + 472348 + 516014 + 455312 + 475721 + 427272 + 538341 + 411282 + 498600 + 523662 := by
      rw [roundedReciprocalBlockSum_171, roundedReciprocalBlockSum_172, roundedReciprocalBlockSum_173, roundedReciprocalBlockSum_174, roundedReciprocalBlockSum_175, roundedReciprocalBlockSum_176, roundedReciprocalBlockSum_177, roundedReciprocalBlockSum_178, roundedReciprocalBlockSum_179, roundedReciprocalBlockSum_180]
    _ = 4828892 := by norm_num

end PrimeFactorUnimodality
