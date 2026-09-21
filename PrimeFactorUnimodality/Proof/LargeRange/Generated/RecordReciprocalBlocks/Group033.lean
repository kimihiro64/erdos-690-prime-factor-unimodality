import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group032
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part330

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 033. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_033 :
    roundedReciprocalBlockSum 320000 330000 = 2548421 := by
  calc
    roundedReciprocalBlockSum 320000 330000 =
        roundedReciprocalBlockSum 320000 321000 +
          roundedReciprocalBlockSum 321000 322000 + roundedReciprocalBlockSum 322000 323000 + roundedReciprocalBlockSum 323000 324000 + roundedReciprocalBlockSum 324000 325000 + roundedReciprocalBlockSum 325000 326000 + roundedReciprocalBlockSum 326000 327000 + roundedReciprocalBlockSum 327000 328000 + roundedReciprocalBlockSum 328000 329000 + roundedReciprocalBlockSum 329000 330000 := by
      rw [roundedReciprocalBlockSum_add_block (show 320000 ≤ 329000 by omega) (show 329000 ≤ 330000 by omega), roundedReciprocalBlockSum_add_block (show 320000 ≤ 328000 by omega) (show 328000 ≤ 329000 by omega), roundedReciprocalBlockSum_add_block (show 320000 ≤ 327000 by omega) (show 327000 ≤ 328000 by omega), roundedReciprocalBlockSum_add_block (show 320000 ≤ 326000 by omega) (show 326000 ≤ 327000 by omega), roundedReciprocalBlockSum_add_block (show 320000 ≤ 325000 by omega) (show 325000 ≤ 326000 by omega), roundedReciprocalBlockSum_add_block (show 320000 ≤ 324000 by omega) (show 324000 ≤ 325000 by omega), roundedReciprocalBlockSum_add_block (show 320000 ≤ 323000 by omega) (show 323000 ≤ 324000 by omega), roundedReciprocalBlockSum_add_block (show 320000 ≤ 322000 by omega) (show 322000 ≤ 323000 by omega), roundedReciprocalBlockSum_add_block (show 320000 ≤ 321000 by omega) (show 321000 ≤ 322000 by omega)]
    _ = 255918 + 264447 + 260519 + 228788 + 280461 + 267321 + 232805 + 268737 + 237489 + 251936 := by
      rw [roundedReciprocalBlockSum_321, roundedReciprocalBlockSum_322, roundedReciprocalBlockSum_323, roundedReciprocalBlockSum_324, roundedReciprocalBlockSum_325, roundedReciprocalBlockSum_326, roundedReciprocalBlockSum_327, roundedReciprocalBlockSum_328, roundedReciprocalBlockSum_329, roundedReciprocalBlockSum_330]
    _ = 2548421 := by norm_num

end PrimeFactorUnimodality
