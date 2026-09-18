import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part131
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part132
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part133
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part134
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part135
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part136
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part137
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part138
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part139
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part140

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 014. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_014 :
    roundedReciprocalBlockSum 130000 140000 = 6306408 := by
  calc
    roundedReciprocalBlockSum 130000 140000 =
        roundedReciprocalBlockSum 130000 131000 +
          roundedReciprocalBlockSum 131000 132000 + roundedReciprocalBlockSum 132000 133000 + roundedReciprocalBlockSum 133000 134000 + roundedReciprocalBlockSum 134000 135000 + roundedReciprocalBlockSum 135000 136000 + roundedReciprocalBlockSum 136000 137000 + roundedReciprocalBlockSum 137000 138000 + roundedReciprocalBlockSum 138000 139000 + roundedReciprocalBlockSum 139000 140000 := by
      rw [roundedReciprocalBlockSum_add_block (show 130000 ≤ 139000 by omega) (show 139000 ≤ 140000 by omega), roundedReciprocalBlockSum_add_block (show 130000 ≤ 138000 by omega) (show 138000 ≤ 139000 by omega), roundedReciprocalBlockSum_add_block (show 130000 ≤ 137000 by omega) (show 137000 ≤ 138000 by omega), roundedReciprocalBlockSum_add_block (show 130000 ≤ 136000 by omega) (show 136000 ≤ 137000 by omega), roundedReciprocalBlockSum_add_block (show 130000 ≤ 135000 by omega) (show 135000 ≤ 136000 by omega), roundedReciprocalBlockSum_add_block (show 130000 ≤ 134000 by omega) (show 134000 ≤ 135000 by omega), roundedReciprocalBlockSum_add_block (show 130000 ≤ 133000 by omega) (show 133000 ≤ 134000 by omega), roundedReciprocalBlockSum_add_block (show 130000 ≤ 132000 by omega) (show 132000 ≤ 133000 by omega), roundedReciprocalBlockSum_add_block (show 130000 ≤ 131000 by omega) (show 131000 ≤ 132000 by omega)]
    _ = 651525 + 631178 + 656553 + 614334 + 594916 + 656951 + 703287 + 581798 + 613807 + 602059 := by
      rw [roundedReciprocalBlockSum_131, roundedReciprocalBlockSum_132, roundedReciprocalBlockSum_133, roundedReciprocalBlockSum_134, roundedReciprocalBlockSum_135, roundedReciprocalBlockSum_136, roundedReciprocalBlockSum_137, roundedReciprocalBlockSum_138, roundedReciprocalBlockSum_139, roundedReciprocalBlockSum_140]
    _ = 6306408 := by norm_num

end PrimeFactorUnimodality
