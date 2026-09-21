import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group045
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part460

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 046. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_046 :
    roundedReciprocalBlockSum 450000 460000 = 1787626 := by
  calc
    roundedReciprocalBlockSum 450000 460000 =
        roundedReciprocalBlockSum 450000 451000 +
          roundedReciprocalBlockSum 451000 452000 + roundedReciprocalBlockSum 452000 453000 + roundedReciprocalBlockSum 453000 454000 + roundedReciprocalBlockSum 454000 455000 + roundedReciprocalBlockSum 455000 456000 + roundedReciprocalBlockSum 456000 457000 + roundedReciprocalBlockSum 457000 458000 + roundedReciprocalBlockSum 458000 459000 + roundedReciprocalBlockSum 459000 460000 := by
      rw [roundedReciprocalBlockSum_add_block (show 450000 ≤ 459000 by omega) (show 459000 ≤ 460000 by omega), roundedReciprocalBlockSum_add_block (show 450000 ≤ 458000 by omega) (show 458000 ≤ 459000 by omega), roundedReciprocalBlockSum_add_block (show 450000 ≤ 457000 by omega) (show 457000 ≤ 458000 by omega), roundedReciprocalBlockSum_add_block (show 450000 ≤ 456000 by omega) (show 456000 ≤ 457000 by omega), roundedReciprocalBlockSum_add_block (show 450000 ≤ 455000 by omega) (show 455000 ≤ 456000 by omega), roundedReciprocalBlockSum_add_block (show 450000 ≤ 454000 by omega) (show 454000 ≤ 455000 by omega), roundedReciprocalBlockSum_add_block (show 450000 ≤ 453000 by omega) (show 453000 ≤ 454000 by omega), roundedReciprocalBlockSum_add_block (show 450000 ≤ 452000 by omega) (show 452000 ≤ 453000 by omega), roundedReciprocalBlockSum_add_block (show 450000 ≤ 451000 by omega) (show 451000 ≤ 452000 by omega)]
    _ = 215367 + 188294 + 145894 + 178644 + 169455 + 199819 + 170901 + 177104 + 183230 + 158918 := by
      rw [roundedReciprocalBlockSum_451, roundedReciprocalBlockSum_452, roundedReciprocalBlockSum_453, roundedReciprocalBlockSum_454, roundedReciprocalBlockSum_455, roundedReciprocalBlockSum_456, roundedReciprocalBlockSum_457, roundedReciprocalBlockSum_458, roundedReciprocalBlockSum_459, roundedReciprocalBlockSum_460]
    _ = 1787626 := by norm_num

end PrimeFactorUnimodality
