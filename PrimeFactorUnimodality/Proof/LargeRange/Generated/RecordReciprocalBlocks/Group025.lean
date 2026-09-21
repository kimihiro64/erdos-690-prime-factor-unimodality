import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group024
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part250

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 025. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_025 :
    roundedReciprocalBlockSum 240000 250000 = 3359885 := by
  calc
    roundedReciprocalBlockSum 240000 250000 =
        roundedReciprocalBlockSum 240000 241000 +
          roundedReciprocalBlockSum 241000 242000 + roundedReciprocalBlockSum 242000 243000 + roundedReciprocalBlockSum 243000 244000 + roundedReciprocalBlockSum 244000 245000 + roundedReciprocalBlockSum 245000 246000 + roundedReciprocalBlockSum 246000 247000 + roundedReciprocalBlockSum 247000 248000 + roundedReciprocalBlockSum 248000 249000 + roundedReciprocalBlockSum 249000 250000 := by
      rw [roundedReciprocalBlockSum_add_block (show 240000 ≤ 249000 by omega) (show 249000 ≤ 250000 by omega), roundedReciprocalBlockSum_add_block (show 240000 ≤ 248000 by omega) (show 248000 ≤ 249000 by omega), roundedReciprocalBlockSum_add_block (show 240000 ≤ 247000 by omega) (show 247000 ≤ 248000 by omega), roundedReciprocalBlockSum_add_block (show 240000 ≤ 246000 by omega) (show 246000 ≤ 247000 by omega), roundedReciprocalBlockSum_add_block (show 240000 ≤ 245000 by omega) (show 245000 ≤ 246000 by omega), roundedReciprocalBlockSum_add_block (show 240000 ≤ 244000 by omega) (show 244000 ≤ 245000 by omega), roundedReciprocalBlockSum_add_block (show 240000 ≤ 243000 by omega) (show 243000 ≤ 244000 by omega), roundedReciprocalBlockSum_add_block (show 240000 ≤ 242000 by omega) (show 242000 ≤ 243000 by omega), roundedReciprocalBlockSum_add_block (show 240000 ≤ 241000 by omega) (show 241000 ≤ 242000 by omega)]
    _ = 332699 + 376822 + 313435 + 316261 + 359974 + 325885 + 340773 + 319186 + 354178 + 320672 := by
      rw [roundedReciprocalBlockSum_241, roundedReciprocalBlockSum_242, roundedReciprocalBlockSum_243, roundedReciprocalBlockSum_244, roundedReciprocalBlockSum_245, roundedReciprocalBlockSum_246, roundedReciprocalBlockSum_247, roundedReciprocalBlockSum_248, roundedReciprocalBlockSum_249, roundedReciprocalBlockSum_250]
    _ = 3359885 := by norm_num

end PrimeFactorUnimodality
