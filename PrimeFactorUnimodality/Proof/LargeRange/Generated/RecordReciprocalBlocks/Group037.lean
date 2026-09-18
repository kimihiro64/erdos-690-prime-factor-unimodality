import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part361
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part362
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part363
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part364
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part365
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part366
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part367
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part368
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part369
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part370

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 037. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_037 :
    roundedReciprocalBlockSum 360000 370000 = 2219825 := by
  calc
    roundedReciprocalBlockSum 360000 370000 =
        roundedReciprocalBlockSum 360000 361000 +
          roundedReciprocalBlockSum 361000 362000 + roundedReciprocalBlockSum 362000 363000 + roundedReciprocalBlockSum 363000 364000 + roundedReciprocalBlockSum 364000 365000 + roundedReciprocalBlockSum 365000 366000 + roundedReciprocalBlockSum 366000 367000 + roundedReciprocalBlockSum 367000 368000 + roundedReciprocalBlockSum 368000 369000 + roundedReciprocalBlockSum 369000 370000 := by
      rw [roundedReciprocalBlockSum_add_block (show 360000 ≤ 369000 by omega) (show 369000 ≤ 370000 by omega), roundedReciprocalBlockSum_add_block (show 360000 ≤ 368000 by omega) (show 368000 ≤ 369000 by omega), roundedReciprocalBlockSum_add_block (show 360000 ≤ 367000 by omega) (show 367000 ≤ 368000 by omega), roundedReciprocalBlockSum_add_block (show 360000 ≤ 366000 by omega) (show 366000 ≤ 367000 by omega), roundedReciprocalBlockSum_add_block (show 360000 ≤ 365000 by omega) (show 365000 ≤ 366000 by omega), roundedReciprocalBlockSum_add_block (show 360000 ≤ 364000 by omega) (show 364000 ≤ 365000 by omega), roundedReciprocalBlockSum_add_block (show 360000 ≤ 363000 by omega) (show 363000 ≤ 364000 by omega), roundedReciprocalBlockSum_add_block (show 360000 ≤ 362000 by omega) (show 362000 ≤ 363000 by omega), roundedReciprocalBlockSum_add_block (show 360000 ≤ 361000 by omega) (show 361000 ≤ 362000 by omega)]
    _ = 205307 + 229631 + 215229 + 242130 + 225001 + 224397 + 240165 + 228635 + 211734 + 197596 := by
      rw [roundedReciprocalBlockSum_361, roundedReciprocalBlockSum_362, roundedReciprocalBlockSum_363, roundedReciprocalBlockSum_364, roundedReciprocalBlockSum_365, roundedReciprocalBlockSum_366, roundedReciprocalBlockSum_367, roundedReciprocalBlockSum_368, roundedReciprocalBlockSum_369, roundedReciprocalBlockSum_370]
    _ = 2219825 := by norm_num

end PrimeFactorUnimodality
