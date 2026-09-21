import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group039
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part400

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 040. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_040 :
    roundedReciprocalBlockSum 390000 400000 = 2129931 := by
  calc
    roundedReciprocalBlockSum 390000 400000 =
        roundedReciprocalBlockSum 390000 391000 +
          roundedReciprocalBlockSum 391000 392000 + roundedReciprocalBlockSum 392000 393000 + roundedReciprocalBlockSum 393000 394000 + roundedReciprocalBlockSum 394000 395000 + roundedReciprocalBlockSum 395000 396000 + roundedReciprocalBlockSum 396000 397000 + roundedReciprocalBlockSum 397000 398000 + roundedReciprocalBlockSum 398000 399000 + roundedReciprocalBlockSum 399000 400000 := by
      rw [roundedReciprocalBlockSum_add_block (show 390000 ≤ 399000 by omega) (show 399000 ≤ 400000 by omega), roundedReciprocalBlockSum_add_block (show 390000 ≤ 398000 by omega) (show 398000 ≤ 399000 by omega), roundedReciprocalBlockSum_add_block (show 390000 ≤ 397000 by omega) (show 397000 ≤ 398000 by omega), roundedReciprocalBlockSum_add_block (show 390000 ≤ 396000 by omega) (show 396000 ≤ 397000 by omega), roundedReciprocalBlockSum_add_block (show 390000 ≤ 395000 by omega) (show 395000 ≤ 396000 by omega), roundedReciprocalBlockSum_add_block (show 390000 ≤ 394000 by omega) (show 394000 ≤ 395000 by omega), roundedReciprocalBlockSum_add_block (show 390000 ≤ 393000 by omega) (show 393000 ≤ 394000 by omega), roundedReciprocalBlockSum_add_block (show 390000 ≤ 392000 by omega) (show 392000 ≤ 393000 by omega), roundedReciprocalBlockSum_add_block (show 390000 ≤ 391000 by omega) (show 391000 ≤ 392000 by omega)]
    _ = 220273 + 212053 + 229345 + 231313 + 207884 + 194739 + 206856 + 196271 + 218383 + 212814 := by
      rw [roundedReciprocalBlockSum_391, roundedReciprocalBlockSum_392, roundedReciprocalBlockSum_393, roundedReciprocalBlockSum_394, roundedReciprocalBlockSum_395, roundedReciprocalBlockSum_396, roundedReciprocalBlockSum_397, roundedReciprocalBlockSum_398, roundedReciprocalBlockSum_399, roundedReciprocalBlockSum_400]
    _ = 2129931 := by norm_num

end PrimeFactorUnimodality
