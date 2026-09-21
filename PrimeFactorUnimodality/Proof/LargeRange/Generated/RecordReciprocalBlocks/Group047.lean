import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group046
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part470

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 047. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_047 :
    roundedReciprocalBlockSum 460000 470000 = 1798167 := by
  calc
    roundedReciprocalBlockSum 460000 470000 =
        roundedReciprocalBlockSum 460000 461000 +
          roundedReciprocalBlockSum 461000 462000 + roundedReciprocalBlockSum 462000 463000 + roundedReciprocalBlockSum 463000 464000 + roundedReciprocalBlockSum 464000 465000 + roundedReciprocalBlockSum 465000 466000 + roundedReciprocalBlockSum 466000 467000 + roundedReciprocalBlockSum 467000 468000 + roundedReciprocalBlockSum 468000 469000 + roundedReciprocalBlockSum 469000 470000 := by
      rw [roundedReciprocalBlockSum_add_block (show 460000 ≤ 469000 by omega) (show 469000 ≤ 470000 by omega), roundedReciprocalBlockSum_add_block (show 460000 ≤ 468000 by omega) (show 468000 ≤ 469000 by omega), roundedReciprocalBlockSum_add_block (show 460000 ≤ 467000 by omega) (show 467000 ≤ 468000 by omega), roundedReciprocalBlockSum_add_block (show 460000 ≤ 466000 by omega) (show 466000 ≤ 467000 by omega), roundedReciprocalBlockSum_add_block (show 460000 ≤ 465000 by omega) (show 465000 ≤ 466000 by omega), roundedReciprocalBlockSum_add_block (show 460000 ≤ 464000 by omega) (show 464000 ≤ 465000 by omega), roundedReciprocalBlockSum_add_block (show 460000 ≤ 463000 by omega) (show 463000 ≤ 464000 by omega), roundedReciprocalBlockSum_add_block (show 460000 ≤ 462000 by omega) (show 462000 ≤ 463000 by omega), roundedReciprocalBlockSum_add_block (show 460000 ≤ 461000 by omega) (show 461000 ≤ 462000 by omega)]
    _ = 182445 + 169048 + 177342 + 183415 + 191638 + 165472 + 169391 + 198973 + 194280 + 166163 := by
      rw [roundedReciprocalBlockSum_461, roundedReciprocalBlockSum_462, roundedReciprocalBlockSum_463, roundedReciprocalBlockSum_464, roundedReciprocalBlockSum_465, roundedReciprocalBlockSum_466, roundedReciprocalBlockSum_467, roundedReciprocalBlockSum_468, roundedReciprocalBlockSum_469, roundedReciprocalBlockSum_470]
    _ = 1798167 := by norm_num

end PrimeFactorUnimodality
