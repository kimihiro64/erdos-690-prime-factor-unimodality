import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part181
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part182
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part183
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part184
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part185
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part186
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part187
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part188
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part189
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part190

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 019. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_019 :
    roundedReciprocalBlockSum 180000 190000 = 4475075 := by
  calc
    roundedReciprocalBlockSum 180000 190000 =
        roundedReciprocalBlockSum 180000 181000 +
          roundedReciprocalBlockSum 181000 182000 + roundedReciprocalBlockSum 182000 183000 + roundedReciprocalBlockSum 183000 184000 + roundedReciprocalBlockSum 184000 185000 + roundedReciprocalBlockSum 185000 186000 + roundedReciprocalBlockSum 186000 187000 + roundedReciprocalBlockSum 187000 188000 + roundedReciprocalBlockSum 188000 189000 + roundedReciprocalBlockSum 189000 190000 := by
      rw [roundedReciprocalBlockSum_add_block (show 180000 ≤ 189000 by omega) (show 189000 ≤ 190000 by omega), roundedReciprocalBlockSum_add_block (show 180000 ≤ 188000 by omega) (show 188000 ≤ 189000 by omega), roundedReciprocalBlockSum_add_block (show 180000 ≤ 187000 by omega) (show 187000 ≤ 188000 by omega), roundedReciprocalBlockSum_add_block (show 180000 ≤ 186000 by omega) (show 186000 ≤ 187000 by omega), roundedReciprocalBlockSum_add_block (show 180000 ≤ 185000 by omega) (show 185000 ≤ 186000 by omega), roundedReciprocalBlockSum_add_block (show 180000 ≤ 184000 by omega) (show 184000 ≤ 185000 by omega), roundedReciprocalBlockSum_add_block (show 180000 ≤ 183000 by omega) (show 183000 ≤ 184000 by omega), roundedReciprocalBlockSum_add_block (show 180000 ≤ 182000 by omega) (show 182000 ≤ 183000 by omega), roundedReciprocalBlockSum_add_block (show 180000 ≤ 181000 by omega) (show 181000 ≤ 182000 by omega)]
    _ = 393504 + 435269 + 498699 + 430549 + 449920 + 490561 + 423720 + 464129 + 424362 + 464362 := by
      rw [roundedReciprocalBlockSum_181, roundedReciprocalBlockSum_182, roundedReciprocalBlockSum_183, roundedReciprocalBlockSum_184, roundedReciprocalBlockSum_185, roundedReciprocalBlockSum_186, roundedReciprocalBlockSum_187, roundedReciprocalBlockSum_188, roundedReciprocalBlockSum_189, roundedReciprocalBlockSum_190]
    _ = 4475075 := by norm_num

end PrimeFactorUnimodality
