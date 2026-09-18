import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part251
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part252
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part253
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part254
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part255
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part256
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part257
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part258
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part259
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part260

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 026. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_026 :
    roundedReciprocalBlockSum 250000 260000 = 3122091 := by
  calc
    roundedReciprocalBlockSum 250000 260000 =
        roundedReciprocalBlockSum 250000 251000 +
          roundedReciprocalBlockSum 251000 252000 + roundedReciprocalBlockSum 252000 253000 + roundedReciprocalBlockSum 253000 254000 + roundedReciprocalBlockSum 254000 255000 + roundedReciprocalBlockSum 255000 256000 + roundedReciprocalBlockSum 256000 257000 + roundedReciprocalBlockSum 257000 258000 + roundedReciprocalBlockSum 258000 259000 + roundedReciprocalBlockSum 259000 260000 := by
      rw [roundedReciprocalBlockSum_add_block (show 250000 ≤ 259000 by omega) (show 259000 ≤ 260000 by omega), roundedReciprocalBlockSum_add_block (show 250000 ≤ 258000 by omega) (show 258000 ≤ 259000 by omega), roundedReciprocalBlockSum_add_block (show 250000 ≤ 257000 by omega) (show 257000 ≤ 258000 by omega), roundedReciprocalBlockSum_add_block (show 250000 ≤ 256000 by omega) (show 256000 ≤ 257000 by omega), roundedReciprocalBlockSum_add_block (show 250000 ≤ 255000 by omega) (show 255000 ≤ 256000 by omega), roundedReciprocalBlockSum_add_block (show 250000 ≤ 254000 by omega) (show 254000 ≤ 255000 by omega), roundedReciprocalBlockSum_add_block (show 250000 ≤ 253000 by omega) (show 253000 ≤ 254000 by omega), roundedReciprocalBlockSum_add_block (show 250000 ≤ 252000 by omega) (show 252000 ≤ 253000 by omega), roundedReciprocalBlockSum_add_block (show 250000 ≤ 251000 by omega) (show 251000 ≤ 252000 by omega)]
    _ = 283445 + 349971 + 308944 + 323446 + 298625 + 340560 + 284669 + 302950 + 332728 + 296753 := by
      rw [roundedReciprocalBlockSum_251, roundedReciprocalBlockSum_252, roundedReciprocalBlockSum_253, roundedReciprocalBlockSum_254, roundedReciprocalBlockSum_255, roundedReciprocalBlockSum_256, roundedReciprocalBlockSum_257, roundedReciprocalBlockSum_258, roundedReciprocalBlockSum_259, roundedReciprocalBlockSum_260]
    _ = 3122091 := by norm_num

end PrimeFactorUnimodality
