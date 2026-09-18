import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part421
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part422
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part423
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part424
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part425
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part426
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part427
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part428
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part429
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part430

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 043. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_043 :
    roundedReciprocalBlockSum 420000 430000 = 1943915 := by
  calc
    roundedReciprocalBlockSum 420000 430000 =
        roundedReciprocalBlockSum 420000 421000 +
          roundedReciprocalBlockSum 421000 422000 + roundedReciprocalBlockSum 422000 423000 + roundedReciprocalBlockSum 423000 424000 + roundedReciprocalBlockSum 424000 425000 + roundedReciprocalBlockSum 425000 426000 + roundedReciprocalBlockSum 426000 427000 + roundedReciprocalBlockSum 427000 428000 + roundedReciprocalBlockSum 428000 429000 + roundedReciprocalBlockSum 429000 430000 := by
      rw [roundedReciprocalBlockSum_add_block (show 420000 ≤ 429000 by omega) (show 429000 ≤ 430000 by omega), roundedReciprocalBlockSum_add_block (show 420000 ≤ 428000 by omega) (show 428000 ≤ 429000 by omega), roundedReciprocalBlockSum_add_block (show 420000 ≤ 427000 by omega) (show 427000 ≤ 428000 by omega), roundedReciprocalBlockSum_add_block (show 420000 ≤ 426000 by omega) (show 426000 ≤ 427000 by omega), roundedReciprocalBlockSum_add_block (show 420000 ≤ 425000 by omega) (show 425000 ≤ 426000 by omega), roundedReciprocalBlockSum_add_block (show 420000 ≤ 424000 by omega) (show 424000 ≤ 425000 by omega), roundedReciprocalBlockSum_add_block (show 420000 ≤ 423000 by omega) (show 423000 ≤ 424000 by omega), roundedReciprocalBlockSum_add_block (show 420000 ≤ 422000 by omega) (show 422000 ≤ 423000 by omega), roundedReciprocalBlockSum_add_block (show 420000 ≤ 421000 by omega) (show 421000 ≤ 422000 by omega)]
    _ = 187911 + 187469 + 205967 + 207844 + 200282 + 181005 + 185265 + 196528 + 177409 + 214235 := by
      rw [roundedReciprocalBlockSum_421, roundedReciprocalBlockSum_422, roundedReciprocalBlockSum_423, roundedReciprocalBlockSum_424, roundedReciprocalBlockSum_425, roundedReciprocalBlockSum_426, roundedReciprocalBlockSum_427, roundedReciprocalBlockSum_428, roundedReciprocalBlockSum_429, roundedReciprocalBlockSum_430]
    _ = 1943915 := by norm_num

end PrimeFactorUnimodality
