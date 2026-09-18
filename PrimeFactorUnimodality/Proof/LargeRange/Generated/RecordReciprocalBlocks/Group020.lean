import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part191
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part192
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part193
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part194
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part195
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part196
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part197
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part198
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part199
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part200

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 020. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_020 :
    roundedReciprocalBlockSum 190000 200000 = 4175051 := by
  calc
    roundedReciprocalBlockSum 190000 200000 =
        roundedReciprocalBlockSum 190000 191000 +
          roundedReciprocalBlockSum 191000 192000 + roundedReciprocalBlockSum 192000 193000 + roundedReciprocalBlockSum 193000 194000 + roundedReciprocalBlockSum 194000 195000 + roundedReciprocalBlockSum 195000 196000 + roundedReciprocalBlockSum 196000 197000 + roundedReciprocalBlockSum 197000 198000 + roundedReciprocalBlockSum 198000 199000 + roundedReciprocalBlockSum 199000 200000 := by
      rw [roundedReciprocalBlockSum_add_block (show 190000 ≤ 199000 by omega) (show 199000 ≤ 200000 by omega), roundedReciprocalBlockSum_add_block (show 190000 ≤ 198000 by omega) (show 198000 ≤ 199000 by omega), roundedReciprocalBlockSum_add_block (show 190000 ≤ 197000 by omega) (show 197000 ≤ 198000 by omega), roundedReciprocalBlockSum_add_block (show 190000 ≤ 196000 by omega) (show 196000 ≤ 197000 by omega), roundedReciprocalBlockSum_add_block (show 190000 ≤ 195000 by omega) (show 195000 ≤ 196000 by omega), roundedReciprocalBlockSum_add_block (show 190000 ≤ 194000 by omega) (show 194000 ≤ 195000 by omega), roundedReciprocalBlockSum_add_block (show 190000 ≤ 193000 by omega) (show 193000 ≤ 194000 by omega), roundedReciprocalBlockSum_add_block (show 190000 ≤ 192000 by omega) (show 192000 ≤ 193000 by omega), roundedReciprocalBlockSum_add_block (show 190000 ≤ 191000 by omega) (show 191000 ≤ 192000 by omega)]
    _ = 393678 + 423023 + 462372 + 434112 + 380460 + 434821 + 386814 + 440567 + 433257 + 385947 := by
      rw [roundedReciprocalBlockSum_191, roundedReciprocalBlockSum_192, roundedReciprocalBlockSum_193, roundedReciprocalBlockSum_194, roundedReciprocalBlockSum_195, roundedReciprocalBlockSum_196, roundedReciprocalBlockSum_197, roundedReciprocalBlockSum_198, roundedReciprocalBlockSum_199, roundedReciprocalBlockSum_200]
    _ = 4175051 := by norm_num

end PrimeFactorUnimodality
