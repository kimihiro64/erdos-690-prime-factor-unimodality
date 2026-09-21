import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group011
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part120

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 012. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_012 :
    roundedReciprocalBlockSum 110000 120000 = 7376979 := by
  calc
    roundedReciprocalBlockSum 110000 120000 =
        roundedReciprocalBlockSum 110000 111000 +
          roundedReciprocalBlockSum 111000 112000 + roundedReciprocalBlockSum 112000 113000 + roundedReciprocalBlockSum 113000 114000 + roundedReciprocalBlockSum 114000 115000 + roundedReciprocalBlockSum 115000 116000 + roundedReciprocalBlockSum 116000 117000 + roundedReciprocalBlockSum 117000 118000 + roundedReciprocalBlockSum 118000 119000 + roundedReciprocalBlockSum 119000 120000 := by
      rw [roundedReciprocalBlockSum_add_block (show 110000 ≤ 119000 by omega) (show 119000 ≤ 120000 by omega), roundedReciprocalBlockSum_add_block (show 110000 ≤ 118000 by omega) (show 118000 ≤ 119000 by omega), roundedReciprocalBlockSum_add_block (show 110000 ≤ 117000 by omega) (show 117000 ≤ 118000 by omega), roundedReciprocalBlockSum_add_block (show 110000 ≤ 116000 by omega) (show 116000 ≤ 117000 by omega), roundedReciprocalBlockSum_add_block (show 110000 ≤ 115000 by omega) (show 115000 ≤ 116000 by omega), roundedReciprocalBlockSum_add_block (show 110000 ≤ 114000 by omega) (show 114000 ≤ 115000 by omega), roundedReciprocalBlockSum_add_block (show 110000 ≤ 113000 by omega) (show 113000 ≤ 114000 by omega), roundedReciprocalBlockSum_add_block (show 110000 ≤ 112000 by omega) (show 112000 ≤ 113000 by omega), roundedReciprocalBlockSum_add_block (show 110000 ≤ 111000 by omega) (show 111000 ≤ 112000 by omega)]
    _ = 750888 + 753261 + 720145 + 775675 + 716255 + 805069 + 695207 + 765849 + 666653 + 727977 := by
      rw [roundedReciprocalBlockSum_111, roundedReciprocalBlockSum_112, roundedReciprocalBlockSum_113, roundedReciprocalBlockSum_114, roundedReciprocalBlockSum_115, roundedReciprocalBlockSum_116, roundedReciprocalBlockSum_117, roundedReciprocalBlockSum_118, roundedReciprocalBlockSum_119, roundedReciprocalBlockSum_120]
    _ = 7376979 := by norm_num

end PrimeFactorUnimodality
