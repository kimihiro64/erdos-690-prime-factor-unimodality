import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group031
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part320

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 032. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_032 :
    roundedReciprocalBlockSum 310000 320000 = 2641414 := by
  calc
    roundedReciprocalBlockSum 310000 320000 =
        roundedReciprocalBlockSum 310000 311000 +
          roundedReciprocalBlockSum 311000 312000 + roundedReciprocalBlockSum 312000 313000 + roundedReciprocalBlockSum 313000 314000 + roundedReciprocalBlockSum 314000 315000 + roundedReciprocalBlockSum 315000 316000 + roundedReciprocalBlockSum 316000 317000 + roundedReciprocalBlockSum 317000 318000 + roundedReciprocalBlockSum 318000 319000 + roundedReciprocalBlockSum 319000 320000 := by
      rw [roundedReciprocalBlockSum_add_block (show 310000 ≤ 319000 by omega) (show 319000 ≤ 320000 by omega), roundedReciprocalBlockSum_add_block (show 310000 ≤ 318000 by omega) (show 318000 ≤ 319000 by omega), roundedReciprocalBlockSum_add_block (show 310000 ≤ 317000 by omega) (show 317000 ≤ 318000 by omega), roundedReciprocalBlockSum_add_block (show 310000 ≤ 316000 by omega) (show 316000 ≤ 317000 by omega), roundedReciprocalBlockSum_add_block (show 310000 ≤ 315000 by omega) (show 315000 ≤ 316000 by omega), roundedReciprocalBlockSum_add_block (show 310000 ≤ 314000 by omega) (show 314000 ≤ 315000 by omega), roundedReciprocalBlockSum_add_block (show 310000 ≤ 313000 by omega) (show 313000 ≤ 314000 by omega), roundedReciprocalBlockSum_add_block (show 310000 ≤ 312000 by omega) (show 312000 ≤ 313000 by omega), roundedReciprocalBlockSum_add_block (show 310000 ≤ 311000 by omega) (show 311000 ≤ 312000 by omega)]
    _ = 264134 + 227978 + 288074 + 283909 + 248070 + 250435 + 274916 + 274045 + 257499 + 272354 := by
      rw [roundedReciprocalBlockSum_311, roundedReciprocalBlockSum_312, roundedReciprocalBlockSum_313, roundedReciprocalBlockSum_314, roundedReciprocalBlockSum_315, roundedReciprocalBlockSum_316, roundedReciprocalBlockSum_317, roundedReciprocalBlockSum_318, roundedReciprocalBlockSum_319, roundedReciprocalBlockSum_320]
    _ = 2641414 := by norm_num

end PrimeFactorUnimodality
