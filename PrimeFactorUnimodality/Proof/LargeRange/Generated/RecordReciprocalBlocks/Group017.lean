import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part161
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part162
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part163
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part164
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part165
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part166
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part167
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part168
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part169
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part170

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 017. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_017 :
    roundedReciprocalBlockSum 160000 170000 = 4936183 := by
  calc
    roundedReciprocalBlockSum 160000 170000 =
        roundedReciprocalBlockSum 160000 161000 +
          roundedReciprocalBlockSum 161000 162000 + roundedReciprocalBlockSum 162000 163000 + roundedReciprocalBlockSum 163000 164000 + roundedReciprocalBlockSum 164000 165000 + roundedReciprocalBlockSum 165000 166000 + roundedReciprocalBlockSum 166000 167000 + roundedReciprocalBlockSum 167000 168000 + roundedReciprocalBlockSum 168000 169000 + roundedReciprocalBlockSum 169000 170000 := by
      rw [roundedReciprocalBlockSum_add_block (show 160000 ≤ 169000 by omega) (show 169000 ≤ 170000 by omega), roundedReciprocalBlockSum_add_block (show 160000 ≤ 168000 by omega) (show 168000 ≤ 169000 by omega), roundedReciprocalBlockSum_add_block (show 160000 ≤ 167000 by omega) (show 167000 ≤ 168000 by omega), roundedReciprocalBlockSum_add_block (show 160000 ≤ 166000 by omega) (show 166000 ≤ 167000 by omega), roundedReciprocalBlockSum_add_block (show 160000 ≤ 165000 by omega) (show 165000 ≤ 166000 by omega), roundedReciprocalBlockSum_add_block (show 160000 ≤ 164000 by omega) (show 164000 ≤ 165000 by omega), roundedReciprocalBlockSum_add_block (show 160000 ≤ 163000 by omega) (show 163000 ≤ 164000 by omega), roundedReciprocalBlockSum_add_block (show 160000 ≤ 162000 by omega) (show 162000 ≤ 163000 by omega), roundedReciprocalBlockSum_add_block (show 160000 ≤ 161000 by omega) (show 161000 ≤ 162000 by omega)]
    _ = 529635 + 520125 + 498353 + 507629 + 468218 + 483441 + 486469 + 495702 + 433302 + 513309 := by
      rw [roundedReciprocalBlockSum_161, roundedReciprocalBlockSum_162, roundedReciprocalBlockSum_163, roundedReciprocalBlockSum_164, roundedReciprocalBlockSum_165, roundedReciprocalBlockSum_166, roundedReciprocalBlockSum_167, roundedReciprocalBlockSum_168, roundedReciprocalBlockSum_169, roundedReciprocalBlockSum_170]
    _ = 4936183 := by norm_num

end PrimeFactorUnimodality
