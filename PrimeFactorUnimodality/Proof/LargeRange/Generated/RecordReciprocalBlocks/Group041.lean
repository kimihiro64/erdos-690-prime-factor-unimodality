import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part401
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part402
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part403
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part404
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part405
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part406
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part407
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part408
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part409
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part410

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 041. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_041 :
    roundedReciprocalBlockSum 400000 410000 = 1990152 := by
  calc
    roundedReciprocalBlockSum 400000 410000 =
        roundedReciprocalBlockSum 400000 401000 +
          roundedReciprocalBlockSum 401000 402000 + roundedReciprocalBlockSum 402000 403000 + roundedReciprocalBlockSum 403000 404000 + roundedReciprocalBlockSum 404000 405000 + roundedReciprocalBlockSum 405000 406000 + roundedReciprocalBlockSum 406000 407000 + roundedReciprocalBlockSum 407000 408000 + roundedReciprocalBlockSum 408000 409000 + roundedReciprocalBlockSum 409000 410000 := by
      rw [roundedReciprocalBlockSum_add_block (show 400000 ≤ 409000 by omega) (show 409000 ≤ 410000 by omega), roundedReciprocalBlockSum_add_block (show 400000 ≤ 408000 by omega) (show 408000 ≤ 409000 by omega), roundedReciprocalBlockSum_add_block (show 400000 ≤ 407000 by omega) (show 407000 ≤ 408000 by omega), roundedReciprocalBlockSum_add_block (show 400000 ≤ 406000 by omega) (show 406000 ≤ 407000 by omega), roundedReciprocalBlockSum_add_block (show 400000 ≤ 405000 by omega) (show 405000 ≤ 406000 by omega), roundedReciprocalBlockSum_add_block (show 400000 ≤ 404000 by omega) (show 404000 ≤ 405000 by omega), roundedReciprocalBlockSum_add_block (show 400000 ≤ 403000 by omega) (show 403000 ≤ 404000 by omega), roundedReciprocalBlockSum_add_block (show 400000 ≤ 402000 by omega) (show 402000 ≤ 403000 by omega), roundedReciprocalBlockSum_add_block (show 400000 ≤ 401000 by omega) (show 401000 ≤ 402000 by omega)]
    _ = 199795 + 184343 + 196315 + 193351 + 195364 + 219520 + 177154 + 206157 + 200777 + 217376 := by
      rw [roundedReciprocalBlockSum_401, roundedReciprocalBlockSum_402, roundedReciprocalBlockSum_403, roundedReciprocalBlockSum_404, roundedReciprocalBlockSum_405, roundedReciprocalBlockSum_406, roundedReciprocalBlockSum_407, roundedReciprocalBlockSum_408, roundedReciprocalBlockSum_409, roundedReciprocalBlockSum_410]
    _ = 1990152 := by norm_num

end PrimeFactorUnimodality
