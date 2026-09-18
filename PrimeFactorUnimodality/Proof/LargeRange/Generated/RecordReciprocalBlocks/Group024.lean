import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part231
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part232
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part233
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part234
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part235
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part236
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part237
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part238
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part239
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part240

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 024. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_024 :
    roundedReciprocalBlockSum 230000 240000 = 3337046 := by
  calc
    roundedReciprocalBlockSum 230000 240000 =
        roundedReciprocalBlockSum 230000 231000 +
          roundedReciprocalBlockSum 231000 232000 + roundedReciprocalBlockSum 232000 233000 + roundedReciprocalBlockSum 233000 234000 + roundedReciprocalBlockSum 234000 235000 + roundedReciprocalBlockSum 235000 236000 + roundedReciprocalBlockSum 236000 237000 + roundedReciprocalBlockSum 237000 238000 + roundedReciprocalBlockSum 238000 239000 + roundedReciprocalBlockSum 239000 240000 := by
      rw [roundedReciprocalBlockSum_add_block (show 230000 ≤ 239000 by omega) (show 239000 ≤ 240000 by omega), roundedReciprocalBlockSum_add_block (show 230000 ≤ 238000 by omega) (show 238000 ≤ 239000 by omega), roundedReciprocalBlockSum_add_block (show 230000 ≤ 237000 by omega) (show 237000 ≤ 238000 by omega), roundedReciprocalBlockSum_add_block (show 230000 ≤ 236000 by omega) (show 236000 ≤ 237000 by omega), roundedReciprocalBlockSum_add_block (show 230000 ≤ 235000 by omega) (show 235000 ≤ 236000 by omega), roundedReciprocalBlockSum_add_block (show 230000 ≤ 234000 by omega) (show 234000 ≤ 235000 by omega), roundedReciprocalBlockSum_add_block (show 230000 ≤ 233000 by omega) (show 233000 ≤ 234000 by omega), roundedReciprocalBlockSum_add_block (show 230000 ≤ 232000 by omega) (show 232000 ≤ 233000 by omega), roundedReciprocalBlockSum_add_block (show 230000 ≤ 231000 by omega) (show 231000 ≤ 232000 by omega)]
    _ = 364491 + 336965 + 326918 + 304095 + 371026 + 310031 + 321370 + 307414 + 364859 + 329877 := by
      rw [roundedReciprocalBlockSum_231, roundedReciprocalBlockSum_232, roundedReciprocalBlockSum_233, roundedReciprocalBlockSum_234, roundedReciprocalBlockSum_235, roundedReciprocalBlockSum_236, roundedReciprocalBlockSum_237, roundedReciprocalBlockSum_238, roundedReciprocalBlockSum_239, roundedReciprocalBlockSum_240]
    _ = 3337046 := by norm_num

end PrimeFactorUnimodality
