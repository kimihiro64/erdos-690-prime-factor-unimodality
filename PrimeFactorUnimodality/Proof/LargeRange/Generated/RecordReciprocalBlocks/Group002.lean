import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part011
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part012
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part013
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part014
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part015
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part016
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part017
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part018
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part019
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part020

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 002. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_002 :
    roundedReciprocalBlockSum 10000 20000 = 71874803 := by
  calc
    roundedReciprocalBlockSum 10000 20000 =
        roundedReciprocalBlockSum 10000 11000 +
          roundedReciprocalBlockSum 11000 12000 + roundedReciprocalBlockSum 12000 13000 + roundedReciprocalBlockSum 13000 14000 + roundedReciprocalBlockSum 14000 15000 + roundedReciprocalBlockSum 15000 16000 + roundedReciprocalBlockSum 16000 17000 + roundedReciprocalBlockSum 17000 18000 + roundedReciprocalBlockSum 18000 19000 + roundedReciprocalBlockSum 19000 20000 := by
      rw [roundedReciprocalBlockSum_add_block (show 10000 ≤ 19000 by omega) (show 19000 ≤ 20000 by omega), roundedReciprocalBlockSum_add_block (show 10000 ≤ 18000 by omega) (show 18000 ≤ 19000 by omega), roundedReciprocalBlockSum_add_block (show 10000 ≤ 17000 by omega) (show 17000 ≤ 18000 by omega), roundedReciprocalBlockSum_add_block (show 10000 ≤ 16000 by omega) (show 16000 ≤ 17000 by omega), roundedReciprocalBlockSum_add_block (show 10000 ≤ 15000 by omega) (show 15000 ≤ 16000 by omega), roundedReciprocalBlockSum_add_block (show 10000 ≤ 14000 by omega) (show 14000 ≤ 15000 by omega), roundedReciprocalBlockSum_add_block (show 10000 ≤ 13000 by omega) (show 13000 ≤ 14000 by omega), roundedReciprocalBlockSum_add_block (show 10000 ≤ 12000 by omega) (show 12000 ≤ 13000 by omega), roundedReciprocalBlockSum_add_block (show 10000 ≤ 11000 by omega) (show 11000 ≤ 12000 by omega)]
    _ = 10110347 + 8952240 + 8722891 + 7782063 + 7025846 + 6971995 + 5940962 + 5942189 + 5093719 + 5332551 := by
      rw [roundedReciprocalBlockSum_011, roundedReciprocalBlockSum_012, roundedReciprocalBlockSum_013, roundedReciprocalBlockSum_014, roundedReciprocalBlockSum_015, roundedReciprocalBlockSum_016, roundedReciprocalBlockSum_017, roundedReciprocalBlockSum_018, roundedReciprocalBlockSum_019, roundedReciprocalBlockSum_020]
    _ = 71874803 := by norm_num

end PrimeFactorUnimodality
