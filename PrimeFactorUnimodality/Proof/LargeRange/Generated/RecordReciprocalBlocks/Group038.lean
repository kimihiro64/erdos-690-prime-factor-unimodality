import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part371
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part372
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part373
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part374
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part375
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part376
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part377
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part378
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part379
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part380

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 038. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_038 :
    roundedReciprocalBlockSum 370000 380000 = 2197580 := by
  calc
    roundedReciprocalBlockSum 370000 380000 =
        roundedReciprocalBlockSum 370000 371000 +
          roundedReciprocalBlockSum 371000 372000 + roundedReciprocalBlockSum 372000 373000 + roundedReciprocalBlockSum 373000 374000 + roundedReciprocalBlockSum 374000 375000 + roundedReciprocalBlockSum 375000 376000 + roundedReciprocalBlockSum 376000 377000 + roundedReciprocalBlockSum 377000 378000 + roundedReciprocalBlockSum 378000 379000 + roundedReciprocalBlockSum 379000 380000 := by
      rw [roundedReciprocalBlockSum_add_block (show 370000 ≤ 379000 by omega) (show 379000 ≤ 380000 by omega), roundedReciprocalBlockSum_add_block (show 370000 ≤ 378000 by omega) (show 378000 ≤ 379000 by omega), roundedReciprocalBlockSum_add_block (show 370000 ≤ 377000 by omega) (show 377000 ≤ 378000 by omega), roundedReciprocalBlockSum_add_block (show 370000 ≤ 376000 by omega) (show 376000 ≤ 377000 by omega), roundedReciprocalBlockSum_add_block (show 370000 ≤ 375000 by omega) (show 375000 ≤ 376000 by omega), roundedReciprocalBlockSum_add_block (show 370000 ≤ 374000 by omega) (show 374000 ≤ 375000 by omega), roundedReciprocalBlockSum_add_block (show 370000 ≤ 373000 by omega) (show 373000 ≤ 374000 by omega), roundedReciprocalBlockSum_add_block (show 370000 ≤ 372000 by omega) (show 372000 ≤ 373000 by omega), roundedReciprocalBlockSum_add_block (show 370000 ≤ 371000 by omega) (show 371000 ≤ 372000 by omega)]
    _ = 205183 + 215397 + 228229 + 208879 + 232341 + 231754 + 228459 + 204011 + 214037 + 229290 := by
      rw [roundedReciprocalBlockSum_371, roundedReciprocalBlockSum_372, roundedReciprocalBlockSum_373, roundedReciprocalBlockSum_374, roundedReciprocalBlockSum_375, roundedReciprocalBlockSum_376, roundedReciprocalBlockSum_377, roundedReciprocalBlockSum_378, roundedReciprocalBlockSum_379, roundedReciprocalBlockSum_380]
    _ = 2197580 := by norm_num

end PrimeFactorUnimodality
