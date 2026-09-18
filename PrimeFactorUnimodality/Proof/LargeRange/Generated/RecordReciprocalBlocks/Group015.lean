import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part141
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part142
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part143
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part144
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part145
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part146
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part147
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part148
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part149
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part150

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 015. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_015 :
    roundedReciprocalBlockSum 140000 150000 = 5780870 := by
  calc
    roundedReciprocalBlockSum 140000 150000 =
        roundedReciprocalBlockSum 140000 141000 +
          roundedReciprocalBlockSum 141000 142000 + roundedReciprocalBlockSum 142000 143000 + roundedReciprocalBlockSum 143000 144000 + roundedReciprocalBlockSum 144000 145000 + roundedReciprocalBlockSum 145000 146000 + roundedReciprocalBlockSum 146000 147000 + roundedReciprocalBlockSum 147000 148000 + roundedReciprocalBlockSum 148000 149000 + roundedReciprocalBlockSum 149000 150000 := by
      rw [roundedReciprocalBlockSum_add_block (show 140000 ≤ 149000 by omega) (show 149000 ≤ 150000 by omega), roundedReciprocalBlockSum_add_block (show 140000 ≤ 148000 by omega) (show 148000 ≤ 149000 by omega), roundedReciprocalBlockSum_add_block (show 140000 ≤ 147000 by omega) (show 147000 ≤ 148000 by omega), roundedReciprocalBlockSum_add_block (show 140000 ≤ 146000 by omega) (show 146000 ≤ 147000 by omega), roundedReciprocalBlockSum_add_block (show 140000 ≤ 145000 by omega) (show 145000 ≤ 146000 by omega), roundedReciprocalBlockSum_add_block (show 140000 ≤ 144000 by omega) (show 144000 ≤ 145000 by omega), roundedReciprocalBlockSum_add_block (show 140000 ≤ 143000 by omega) (show 143000 ≤ 144000 by omega), roundedReciprocalBlockSum_add_block (show 140000 ≤ 142000 by omega) (show 142000 ≤ 143000 by omega), roundedReciprocalBlockSum_add_block (show 140000 ≤ 141000 by omega) (show 141000 ≤ 142000 by omega)]
    _ = 619173 + 614825 + 575466 + 536503 + 546702 + 584193 + 573457 + 562817 + 558887 + 608847 := by
      rw [roundedReciprocalBlockSum_141, roundedReciprocalBlockSum_142, roundedReciprocalBlockSum_143, roundedReciprocalBlockSum_144, roundedReciprocalBlockSum_145, roundedReciprocalBlockSum_146, roundedReciprocalBlockSum_147, roundedReciprocalBlockSum_148, roundedReciprocalBlockSum_149, roundedReciprocalBlockSum_150]
    _ = 5780870 := by norm_num

end PrimeFactorUnimodality
