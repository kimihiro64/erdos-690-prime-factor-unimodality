import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group009
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part100

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 010. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_010 :
    roundedReciprocalBlockSum 90000 100000 = 9265613 := by
  calc
    roundedReciprocalBlockSum 90000 100000 =
        roundedReciprocalBlockSum 90000 91000 +
          roundedReciprocalBlockSum 91000 92000 + roundedReciprocalBlockSum 92000 93000 + roundedReciprocalBlockSum 93000 94000 + roundedReciprocalBlockSum 94000 95000 + roundedReciprocalBlockSum 95000 96000 + roundedReciprocalBlockSum 96000 97000 + roundedReciprocalBlockSum 97000 98000 + roundedReciprocalBlockSum 98000 99000 + roundedReciprocalBlockSum 99000 100000 := by
      rw [roundedReciprocalBlockSum_add_block (show 90000 ≤ 99000 by omega) (show 99000 ≤ 100000 by omega), roundedReciprocalBlockSum_add_block (show 90000 ≤ 98000 by omega) (show 98000 ≤ 99000 by omega), roundedReciprocalBlockSum_add_block (show 90000 ≤ 97000 by omega) (show 97000 ≤ 98000 by omega), roundedReciprocalBlockSum_add_block (show 90000 ≤ 96000 by omega) (show 96000 ≤ 97000 by omega), roundedReciprocalBlockSum_add_block (show 90000 ≤ 95000 by omega) (show 95000 ≤ 96000 by omega), roundedReciprocalBlockSum_add_block (show 90000 ≤ 94000 by omega) (show 94000 ≤ 95000 by omega), roundedReciprocalBlockSum_add_block (show 90000 ≤ 93000 by omega) (show 93000 ≤ 94000 by omega), roundedReciprocalBlockSum_add_block (show 90000 ≤ 92000 by omega) (show 92000 ≤ 93000 by omega), roundedReciprocalBlockSum_add_block (show 90000 ≤ 91000 by omega) (show 91000 ≤ 92000 by omega)]
    _ = 983812 + 929076 + 1048574 + 919850 + 920663 + 994888 + 870400 + 840988 + 882954 + 874408 := by
      rw [roundedReciprocalBlockSum_091, roundedReciprocalBlockSum_092, roundedReciprocalBlockSum_093, roundedReciprocalBlockSum_094, roundedReciprocalBlockSum_095, roundedReciprocalBlockSum_096, roundedReciprocalBlockSum_097, roundedReciprocalBlockSum_098, roundedReciprocalBlockSum_099, roundedReciprocalBlockSum_100]
    _ = 9265613 := by norm_num

end PrimeFactorUnimodality
