import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group020
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part210

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 021. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_021 :
    roundedReciprocalBlockSum 200000 210000 = 4014029 := by
  calc
    roundedReciprocalBlockSum 200000 210000 =
        roundedReciprocalBlockSum 200000 201000 +
          roundedReciprocalBlockSum 201000 202000 + roundedReciprocalBlockSum 202000 203000 + roundedReciprocalBlockSum 203000 204000 + roundedReciprocalBlockSum 204000 205000 + roundedReciprocalBlockSum 205000 206000 + roundedReciprocalBlockSum 206000 207000 + roundedReciprocalBlockSum 207000 208000 + roundedReciprocalBlockSum 208000 209000 + roundedReciprocalBlockSum 209000 210000 := by
      rw [roundedReciprocalBlockSum_add_block (show 200000 ≤ 209000 by omega) (show 209000 ≤ 210000 by omega), roundedReciprocalBlockSum_add_block (show 200000 ≤ 208000 by omega) (show 208000 ≤ 209000 by omega), roundedReciprocalBlockSum_add_block (show 200000 ≤ 207000 by omega) (show 207000 ≤ 208000 by omega), roundedReciprocalBlockSum_add_block (show 200000 ≤ 206000 by omega) (show 206000 ≤ 207000 by omega), roundedReciprocalBlockSum_add_block (show 200000 ≤ 205000 by omega) (show 205000 ≤ 206000 by omega), roundedReciprocalBlockSum_add_block (show 200000 ≤ 204000 by omega) (show 204000 ≤ 205000 by omega), roundedReciprocalBlockSum_add_block (show 200000 ≤ 203000 by omega) (show 203000 ≤ 204000 by omega), roundedReciprocalBlockSum_add_block (show 200000 ≤ 202000 by omega) (show 202000 ≤ 203000 by omega), roundedReciprocalBlockSum_add_block (show 200000 ≤ 201000 by omega) (show 201000 ≤ 202000 by omega)]
    _ = 384097 + 431720 + 385189 + 383299 + 376571 + 403963 + 402048 + 419333 + 407752 + 420057 := by
      rw [roundedReciprocalBlockSum_201, roundedReciprocalBlockSum_202, roundedReciprocalBlockSum_203, roundedReciprocalBlockSum_204, roundedReciprocalBlockSum_205, roundedReciprocalBlockSum_206, roundedReciprocalBlockSum_207, roundedReciprocalBlockSum_208, roundedReciprocalBlockSum_209, roundedReciprocalBlockSum_210]
    _ = 4014029 := by norm_num

end PrimeFactorUnimodality
