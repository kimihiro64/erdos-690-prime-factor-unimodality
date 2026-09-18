import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part291
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part292
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part293
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part294
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part295
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part296
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part297
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part298
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part299
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part300

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 030. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_030 :
    roundedReciprocalBlockSum 290000 300000 = 2679041 := by
  calc
    roundedReciprocalBlockSum 290000 300000 =
        roundedReciprocalBlockSum 290000 291000 +
          roundedReciprocalBlockSum 291000 292000 + roundedReciprocalBlockSum 292000 293000 + roundedReciprocalBlockSum 293000 294000 + roundedReciprocalBlockSum 294000 295000 + roundedReciprocalBlockSum 295000 296000 + roundedReciprocalBlockSum 296000 297000 + roundedReciprocalBlockSum 297000 298000 + roundedReciprocalBlockSum 298000 299000 + roundedReciprocalBlockSum 299000 300000 := by
      rw [roundedReciprocalBlockSum_add_block (show 290000 ≤ 299000 by omega) (show 299000 ≤ 300000 by omega), roundedReciprocalBlockSum_add_block (show 290000 ≤ 298000 by omega) (show 298000 ≤ 299000 by omega), roundedReciprocalBlockSum_add_block (show 290000 ≤ 297000 by omega) (show 297000 ≤ 298000 by omega), roundedReciprocalBlockSum_add_block (show 290000 ≤ 296000 by omega) (show 296000 ≤ 297000 by omega), roundedReciprocalBlockSum_add_block (show 290000 ≤ 295000 by omega) (show 295000 ≤ 296000 by omega), roundedReciprocalBlockSum_add_block (show 290000 ≤ 294000 by omega) (show 294000 ≤ 295000 by omega), roundedReciprocalBlockSum_add_block (show 290000 ≤ 293000 by omega) (show 293000 ≤ 294000 by omega), roundedReciprocalBlockSum_add_block (show 290000 ≤ 292000 by omega) (show 292000 ≤ 293000 by omega), roundedReciprocalBlockSum_add_block (show 290000 ≤ 291000 by omega) (show 291000 ≤ 292000 by omega)]
    _ = 299538 + 267634 + 270119 + 238538 + 292069 + 260589 + 279954 + 252122 + 254658 + 263820 := by
      rw [roundedReciprocalBlockSum_291, roundedReciprocalBlockSum_292, roundedReciprocalBlockSum_293, roundedReciprocalBlockSum_294, roundedReciprocalBlockSum_295, roundedReciprocalBlockSum_296, roundedReciprocalBlockSum_297, roundedReciprocalBlockSum_298, roundedReciprocalBlockSum_299, roundedReciprocalBlockSum_300]
    _ = 2679041 := by norm_num

end PrimeFactorUnimodality
