import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group008
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part090

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 009. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_009 :
    roundedReciprocalBlockSum 80000 90000 = 10321309 := by
  calc
    roundedReciprocalBlockSum 80000 90000 =
        roundedReciprocalBlockSum 80000 81000 +
          roundedReciprocalBlockSum 81000 82000 + roundedReciprocalBlockSum 82000 83000 + roundedReciprocalBlockSum 83000 84000 + roundedReciprocalBlockSum 84000 85000 + roundedReciprocalBlockSum 85000 86000 + roundedReciprocalBlockSum 86000 87000 + roundedReciprocalBlockSum 87000 88000 + roundedReciprocalBlockSum 88000 89000 + roundedReciprocalBlockSum 89000 90000 := by
      rw [roundedReciprocalBlockSum_add_block (show 80000 ≤ 89000 by omega) (show 89000 ≤ 90000 by omega), roundedReciprocalBlockSum_add_block (show 80000 ≤ 88000 by omega) (show 88000 ≤ 89000 by omega), roundedReciprocalBlockSum_add_block (show 80000 ≤ 87000 by omega) (show 87000 ≤ 88000 by omega), roundedReciprocalBlockSum_add_block (show 80000 ≤ 86000 by omega) (show 86000 ≤ 87000 by omega), roundedReciprocalBlockSum_add_block (show 80000 ≤ 85000 by omega) (show 85000 ≤ 86000 by omega), roundedReciprocalBlockSum_add_block (show 80000 ≤ 84000 by omega) (show 84000 ≤ 85000 by omega), roundedReciprocalBlockSum_add_block (show 80000 ≤ 83000 by omega) (show 83000 ≤ 84000 by omega), roundedReciprocalBlockSum_add_block (show 80000 ≤ 82000 by omega) (show 82000 ≤ 83000 by omega), roundedReciprocalBlockSum_add_block (show 80000 ≤ 81000 by omega) (show 81000 ≤ 82000 by omega)]
    _ = 1093022 + 1129160 + 1079262 + 1006238 + 1029825 + 994480 + 1017670 + 1062799 + 858423 + 1050430 := by
      rw [roundedReciprocalBlockSum_081, roundedReciprocalBlockSum_082, roundedReciprocalBlockSum_083, roundedReciprocalBlockSum_084, roundedReciprocalBlockSum_085, roundedReciprocalBlockSum_086, roundedReciprocalBlockSum_087, roundedReciprocalBlockSum_088, roundedReciprocalBlockSum_089, roundedReciprocalBlockSum_090]
    _ = 10321309 := by norm_num

end PrimeFactorUnimodality
