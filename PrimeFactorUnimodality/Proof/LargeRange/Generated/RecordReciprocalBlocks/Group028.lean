import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group027
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part280

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 028. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_028 :
    roundedReciprocalBlockSum 270000 280000 = 2899569 := by
  calc
    roundedReciprocalBlockSum 270000 280000 =
        roundedReciprocalBlockSum 270000 271000 +
          roundedReciprocalBlockSum 271000 272000 + roundedReciprocalBlockSum 272000 273000 + roundedReciprocalBlockSum 273000 274000 + roundedReciprocalBlockSum 274000 275000 + roundedReciprocalBlockSum 275000 276000 + roundedReciprocalBlockSum 276000 277000 + roundedReciprocalBlockSum 277000 278000 + roundedReciprocalBlockSum 278000 279000 + roundedReciprocalBlockSum 279000 280000 := by
      rw [roundedReciprocalBlockSum_add_block (show 270000 ≤ 279000 by omega) (show 279000 ≤ 280000 by omega), roundedReciprocalBlockSum_add_block (show 270000 ≤ 278000 by omega) (show 278000 ≤ 279000 by omega), roundedReciprocalBlockSum_add_block (show 270000 ≤ 277000 by omega) (show 277000 ≤ 278000 by omega), roundedReciprocalBlockSum_add_block (show 270000 ≤ 276000 by omega) (show 276000 ≤ 277000 by omega), roundedReciprocalBlockSum_add_block (show 270000 ≤ 275000 by omega) (show 275000 ≤ 276000 by omega), roundedReciprocalBlockSum_add_block (show 270000 ≤ 274000 by omega) (show 274000 ≤ 275000 by omega), roundedReciprocalBlockSum_add_block (show 270000 ≤ 273000 by omega) (show 273000 ≤ 274000 by omega), roundedReciprocalBlockSum_add_block (show 270000 ≤ 272000 by omega) (show 272000 ≤ 273000 by omega), roundedReciprocalBlockSum_add_block (show 270000 ≤ 271000 by omega) (show 271000 ≤ 272000 by omega)]
    _ = 310591 + 291025 + 311986 + 263296 + 291469 + 308570 + 300235 + 266706 + 294471 + 261220 := by
      rw [roundedReciprocalBlockSum_271, roundedReciprocalBlockSum_272, roundedReciprocalBlockSum_273, roundedReciprocalBlockSum_274, roundedReciprocalBlockSum_275, roundedReciprocalBlockSum_276, roundedReciprocalBlockSum_277, roundedReciprocalBlockSum_278, roundedReciprocalBlockSum_279, roundedReciprocalBlockSum_280]
    _ = 2899569 := by norm_num

end PrimeFactorUnimodality
