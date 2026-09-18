import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part341
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part342
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part343
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part344
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part345
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part346
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part347
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part348
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part349
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part350

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 035. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_035 :
    roundedReciprocalBlockSum 340000 350000 = 2406511 := by
  calc
    roundedReciprocalBlockSum 340000 350000 =
        roundedReciprocalBlockSum 340000 341000 +
          roundedReciprocalBlockSum 341000 342000 + roundedReciprocalBlockSum 342000 343000 + roundedReciprocalBlockSum 343000 344000 + roundedReciprocalBlockSum 344000 345000 + roundedReciprocalBlockSum 345000 346000 + roundedReciprocalBlockSum 346000 347000 + roundedReciprocalBlockSum 347000 348000 + roundedReciprocalBlockSum 348000 349000 + roundedReciprocalBlockSum 349000 350000 := by
      rw [roundedReciprocalBlockSum_add_block (show 340000 ≤ 349000 by omega) (show 349000 ≤ 350000 by omega), roundedReciprocalBlockSum_add_block (show 340000 ≤ 348000 by omega) (show 348000 ≤ 349000 by omega), roundedReciprocalBlockSum_add_block (show 340000 ≤ 347000 by omega) (show 347000 ≤ 348000 by omega), roundedReciprocalBlockSum_add_block (show 340000 ≤ 346000 by omega) (show 346000 ≤ 347000 by omega), roundedReciprocalBlockSum_add_block (show 340000 ≤ 345000 by omega) (show 345000 ≤ 346000 by omega), roundedReciprocalBlockSum_add_block (show 340000 ≤ 344000 by omega) (show 344000 ≤ 345000 by omega), roundedReciprocalBlockSum_add_block (show 340000 ≤ 343000 by omega) (show 343000 ≤ 344000 by omega), roundedReciprocalBlockSum_add_block (show 340000 ≤ 342000 by omega) (show 342000 ≤ 343000 by omega), roundedReciprocalBlockSum_add_block (show 340000 ≤ 341000 by omega) (show 341000 ≤ 342000 by omega)]
    _ = 255544 + 240151 + 233640 + 244582 + 246768 + 234471 + 239590 + 247520 + 229599 + 234646 := by
      rw [roundedReciprocalBlockSum_341, roundedReciprocalBlockSum_342, roundedReciprocalBlockSum_343, roundedReciprocalBlockSum_344, roundedReciprocalBlockSum_345, roundedReciprocalBlockSum_346, roundedReciprocalBlockSum_347, roundedReciprocalBlockSum_348, roundedReciprocalBlockSum_349, roundedReciprocalBlockSum_350]
    _ = 2406511 := by norm_num

end PrimeFactorUnimodality
