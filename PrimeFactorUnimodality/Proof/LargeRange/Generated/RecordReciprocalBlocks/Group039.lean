import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part381
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part382
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part383
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part384
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part385
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part386
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part387
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part388
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part389
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part390

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 039. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_039 :
    roundedReciprocalBlockSum 380000 390000 = 2127596 := by
  calc
    roundedReciprocalBlockSum 380000 390000 =
        roundedReciprocalBlockSum 380000 381000 +
          roundedReciprocalBlockSum 381000 382000 + roundedReciprocalBlockSum 382000 383000 + roundedReciprocalBlockSum 383000 384000 + roundedReciprocalBlockSum 384000 385000 + roundedReciprocalBlockSum 385000 386000 + roundedReciprocalBlockSum 386000 387000 + roundedReciprocalBlockSum 387000 388000 + roundedReciprocalBlockSum 388000 389000 + roundedReciprocalBlockSum 389000 390000 := by
      rw [roundedReciprocalBlockSum_add_block (show 380000 ≤ 389000 by omega) (show 389000 ≤ 390000 by omega), roundedReciprocalBlockSum_add_block (show 380000 ≤ 388000 by omega) (show 388000 ≤ 389000 by omega), roundedReciprocalBlockSum_add_block (show 380000 ≤ 387000 by omega) (show 387000 ≤ 388000 by omega), roundedReciprocalBlockSum_add_block (show 380000 ≤ 386000 by omega) (show 386000 ≤ 387000 by omega), roundedReciprocalBlockSum_add_block (show 380000 ≤ 385000 by omega) (show 385000 ≤ 386000 by omega), roundedReciprocalBlockSum_add_block (show 380000 ≤ 384000 by omega) (show 384000 ≤ 385000 by omega), roundedReciprocalBlockSum_add_block (show 380000 ≤ 383000 by omega) (show 383000 ≤ 384000 by omega), roundedReciprocalBlockSum_add_block (show 380000 ≤ 382000 by omega) (show 382000 ≤ 383000 by omega), roundedReciprocalBlockSum_add_block (show 380000 ≤ 381000 by omega) (show 381000 ≤ 382000 by omega)]
    _ = 205034 + 212369 + 201330 + 232115 + 210716 + 220554 + 217390 + 191011 + 211106 + 225971 := by
      rw [roundedReciprocalBlockSum_381, roundedReciprocalBlockSum_382, roundedReciprocalBlockSum_383, roundedReciprocalBlockSum_384, roundedReciprocalBlockSum_385, roundedReciprocalBlockSum_386, roundedReciprocalBlockSum_387, roundedReciprocalBlockSum_388, roundedReciprocalBlockSum_389, roundedReciprocalBlockSum_390]
    _ = 2127596 := by norm_num

end PrimeFactorUnimodality
