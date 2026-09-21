import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group015
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part160

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 016. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_016 :
    roundedReciprocalBlockSum 150000 160000 = 5391505 := by
  calc
    roundedReciprocalBlockSum 150000 160000 =
        roundedReciprocalBlockSum 150000 151000 +
          roundedReciprocalBlockSum 151000 152000 + roundedReciprocalBlockSum 152000 153000 + roundedReciprocalBlockSum 153000 154000 + roundedReciprocalBlockSum 154000 155000 + roundedReciprocalBlockSum 155000 156000 + roundedReciprocalBlockSum 156000 157000 + roundedReciprocalBlockSum 157000 158000 + roundedReciprocalBlockSum 158000 159000 + roundedReciprocalBlockSum 159000 160000 := by
      rw [roundedReciprocalBlockSum_add_block (show 150000 ≤ 159000 by omega) (show 159000 ≤ 160000 by omega), roundedReciprocalBlockSum_add_block (show 150000 ≤ 158000 by omega) (show 158000 ≤ 159000 by omega), roundedReciprocalBlockSum_add_block (show 150000 ≤ 157000 by omega) (show 157000 ≤ 158000 by omega), roundedReciprocalBlockSum_add_block (show 150000 ≤ 156000 by omega) (show 156000 ≤ 157000 by omega), roundedReciprocalBlockSum_add_block (show 150000 ≤ 155000 by omega) (show 155000 ≤ 156000 by omega), roundedReciprocalBlockSum_add_block (show 150000 ≤ 154000 by omega) (show 154000 ≤ 155000 by omega), roundedReciprocalBlockSum_add_block (show 150000 ≤ 153000 by omega) (show 153000 ≤ 154000 by omega), roundedReciprocalBlockSum_add_block (show 150000 ≤ 152000 by omega) (show 152000 ≤ 153000 by omega), roundedReciprocalBlockSum_add_block (show 150000 ≤ 151000 by omega) (show 151000 ≤ 152000 by omega)]
    _ = 564840 + 594113 + 577051 + 501642 + 543776 + 546724 + 485670 + 558900 + 485855 + 532934 := by
      rw [roundedReciprocalBlockSum_151, roundedReciprocalBlockSum_152, roundedReciprocalBlockSum_153, roundedReciprocalBlockSum_154, roundedReciprocalBlockSum_155, roundedReciprocalBlockSum_156, roundedReciprocalBlockSum_157, roundedReciprocalBlockSum_158, roundedReciprocalBlockSum_159, roundedReciprocalBlockSum_160]
    _ = 5391505 := by norm_num

end PrimeFactorUnimodality
