import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group028
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part290

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 029. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_029 :
    roundedReciprocalBlockSum 280000 290000 = 2819004 := by
  calc
    roundedReciprocalBlockSum 280000 290000 =
        roundedReciprocalBlockSum 280000 281000 +
          roundedReciprocalBlockSum 281000 282000 + roundedReciprocalBlockSum 282000 283000 + roundedReciprocalBlockSum 283000 284000 + roundedReciprocalBlockSum 284000 285000 + roundedReciprocalBlockSum 285000 286000 + roundedReciprocalBlockSum 286000 287000 + roundedReciprocalBlockSum 287000 288000 + roundedReciprocalBlockSum 288000 289000 + roundedReciprocalBlockSum 289000 290000 := by
      rw [roundedReciprocalBlockSum_add_block (show 280000 ≤ 289000 by omega) (show 289000 ≤ 290000 by omega), roundedReciprocalBlockSum_add_block (show 280000 ≤ 288000 by omega) (show 288000 ≤ 289000 by omega), roundedReciprocalBlockSum_add_block (show 280000 ≤ 287000 by omega) (show 287000 ≤ 288000 by omega), roundedReciprocalBlockSum_add_block (show 280000 ≤ 286000 by omega) (show 286000 ≤ 287000 by omega), roundedReciprocalBlockSum_add_block (show 280000 ≤ 285000 by omega) (show 285000 ≤ 286000 by omega), roundedReciprocalBlockSum_add_block (show 280000 ≤ 284000 by omega) (show 284000 ≤ 285000 by omega), roundedReciprocalBlockSum_add_block (show 280000 ≤ 283000 by omega) (show 283000 ≤ 284000 by omega), roundedReciprocalBlockSum_add_block (show 280000 ≤ 282000 by omega) (show 282000 ≤ 283000 by omega), roundedReciprocalBlockSum_add_block (show 280000 ≤ 281000 by omega) (show 281000 ≤ 282000 by omega)]
    _ = 313747 + 305507 + 276138 + 261070 + 319902 + 269744 + 258325 + 250509 + 266921 + 297141 := by
      rw [roundedReciprocalBlockSum_281, roundedReciprocalBlockSum_282, roundedReciprocalBlockSum_283, roundedReciprocalBlockSum_284, roundedReciprocalBlockSum_285, roundedReciprocalBlockSum_286, roundedReciprocalBlockSum_287, roundedReciprocalBlockSum_288, roundedReciprocalBlockSum_289, roundedReciprocalBlockSum_290]
    _ = 2819004 := by norm_num

end PrimeFactorUnimodality
