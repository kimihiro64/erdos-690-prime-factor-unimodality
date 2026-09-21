import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group022
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part230

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 023. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_023 :
    roundedReciprocalBlockSum 220000 230000 = 3639683 := by
  calc
    roundedReciprocalBlockSum 220000 230000 =
        roundedReciprocalBlockSum 220000 221000 +
          roundedReciprocalBlockSum 221000 222000 + roundedReciprocalBlockSum 222000 223000 + roundedReciprocalBlockSum 223000 224000 + roundedReciprocalBlockSum 224000 225000 + roundedReciprocalBlockSum 225000 226000 + roundedReciprocalBlockSum 226000 227000 + roundedReciprocalBlockSum 227000 228000 + roundedReciprocalBlockSum 228000 229000 + roundedReciprocalBlockSum 229000 230000 := by
      rw [roundedReciprocalBlockSum_add_block (show 220000 ≤ 229000 by omega) (show 229000 ≤ 230000 by omega), roundedReciprocalBlockSum_add_block (show 220000 ≤ 228000 by omega) (show 228000 ≤ 229000 by omega), roundedReciprocalBlockSum_add_block (show 220000 ≤ 227000 by omega) (show 227000 ≤ 228000 by omega), roundedReciprocalBlockSum_add_block (show 220000 ≤ 226000 by omega) (show 226000 ≤ 227000 by omega), roundedReciprocalBlockSum_add_block (show 220000 ≤ 225000 by omega) (show 225000 ≤ 226000 by omega), roundedReciprocalBlockSum_add_block (show 220000 ≤ 224000 by omega) (show 224000 ≤ 225000 by omega), roundedReciprocalBlockSum_add_block (show 220000 ≤ 223000 by omega) (show 223000 ≤ 224000 by omega), roundedReciprocalBlockSum_add_block (show 220000 ≤ 222000 by omega) (show 222000 ≤ 223000 by omega), roundedReciprocalBlockSum_add_block (show 220000 ≤ 221000 by omega) (show 221000 ≤ 222000 by omega)]
    _ = 353736 + 361209 + 364101 + 358045 + 369770 + 372550 + 335591 + 351727 + 389499 + 383455 := by
      rw [roundedReciprocalBlockSum_221, roundedReciprocalBlockSum_222, roundedReciprocalBlockSum_223, roundedReciprocalBlockSum_224, roundedReciprocalBlockSum_225, roundedReciprocalBlockSum_226, roundedReciprocalBlockSum_227, roundedReciprocalBlockSum_228, roundedReciprocalBlockSum_229, roundedReciprocalBlockSum_230]
    _ = 3639683 := by norm_num

end PrimeFactorUnimodality
