import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part101
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part102
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part103
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part104
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part105
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part106
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part107
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part108
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part109
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part110

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 011. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_011 :
    roundedReciprocalBlockSum 100000 110000 = 8205464 := by
  calc
    roundedReciprocalBlockSum 100000 110000 =
        roundedReciprocalBlockSum 100000 101000 +
          roundedReciprocalBlockSum 101000 102000 + roundedReciprocalBlockSum 102000 103000 + roundedReciprocalBlockSum 103000 104000 + roundedReciprocalBlockSum 104000 105000 + roundedReciprocalBlockSum 105000 106000 + roundedReciprocalBlockSum 106000 107000 + roundedReciprocalBlockSum 107000 108000 + roundedReciprocalBlockSum 108000 109000 + roundedReciprocalBlockSum 109000 110000 := by
      rw [roundedReciprocalBlockSum_add_block (show 100000 ≤ 109000 by omega) (show 109000 ≤ 110000 by omega), roundedReciprocalBlockSum_add_block (show 100000 ≤ 108000 by omega) (show 108000 ≤ 109000 by omega), roundedReciprocalBlockSum_add_block (show 100000 ≤ 107000 by omega) (show 107000 ≤ 108000 by omega), roundedReciprocalBlockSum_add_block (show 100000 ≤ 106000 by omega) (show 106000 ≤ 107000 by omega), roundedReciprocalBlockSum_add_block (show 100000 ≤ 105000 by omega) (show 105000 ≤ 106000 by omega), roundedReciprocalBlockSum_add_block (show 100000 ≤ 104000 by omega) (show 104000 ≤ 105000 by omega), roundedReciprocalBlockSum_add_block (show 100000 ≤ 103000 by omega) (show 103000 ≤ 104000 by omega), roundedReciprocalBlockSum_add_block (show 100000 ≤ 102000 by omega) (show 102000 ≤ 103000 by omega), roundedReciprocalBlockSum_add_block (show 100000 ≤ 101000 by omega) (show 101000 ≤ 102000 by omega)]
    _ = 805990 + 916331 + 849203 + 772827 + 870806 + 777211 + 863759 + 706939 + 838684 + 803714 := by
      rw [roundedReciprocalBlockSum_101, roundedReciprocalBlockSum_102, roundedReciprocalBlockSum_103, roundedReciprocalBlockSum_104, roundedReciprocalBlockSum_105, roundedReciprocalBlockSum_106, roundedReciprocalBlockSum_107, roundedReciprocalBlockSum_108, roundedReciprocalBlockSum_109, roundedReciprocalBlockSum_110]
    _ = 8205464 := by norm_num

end PrimeFactorUnimodality
