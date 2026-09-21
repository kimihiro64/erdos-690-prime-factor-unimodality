import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group026
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part270

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 027. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_027 :
    roundedReciprocalBlockSum 260000 270000 = 3052837 := by
  calc
    roundedReciprocalBlockSum 260000 270000 =
        roundedReciprocalBlockSum 260000 261000 +
          roundedReciprocalBlockSum 261000 262000 + roundedReciprocalBlockSum 262000 263000 + roundedReciprocalBlockSum 263000 264000 + roundedReciprocalBlockSum 264000 265000 + roundedReciprocalBlockSum 265000 266000 + roundedReciprocalBlockSum 266000 267000 + roundedReciprocalBlockSum 267000 268000 + roundedReciprocalBlockSum 268000 269000 + roundedReciprocalBlockSum 269000 270000 := by
      rw [roundedReciprocalBlockSum_add_block (show 260000 ≤ 269000 by omega) (show 269000 ≤ 270000 by omega), roundedReciprocalBlockSum_add_block (show 260000 ≤ 268000 by omega) (show 268000 ≤ 269000 by omega), roundedReciprocalBlockSum_add_block (show 260000 ≤ 267000 by omega) (show 267000 ≤ 268000 by omega), roundedReciprocalBlockSum_add_block (show 260000 ≤ 266000 by omega) (show 266000 ≤ 267000 by omega), roundedReciprocalBlockSum_add_block (show 260000 ≤ 265000 by omega) (show 265000 ≤ 266000 by omega), roundedReciprocalBlockSum_add_block (show 260000 ≤ 264000 by omega) (show 264000 ≤ 265000 by omega), roundedReciprocalBlockSum_add_block (show 260000 ≤ 263000 by omega) (show 263000 ≤ 264000 by omega), roundedReciprocalBlockSum_add_block (show 260000 ≤ 262000 by omega) (show 262000 ≤ 263000 by omega), roundedReciprocalBlockSum_add_block (show 260000 ≤ 261000 by omega) (show 261000 ≤ 262000 by omega)]
    _ = 295611 + 279209 + 304835 + 322628 + 302486 + 297608 + 330257 + 351409 + 279301 + 289493 := by
      rw [roundedReciprocalBlockSum_261, roundedReciprocalBlockSum_262, roundedReciprocalBlockSum_263, roundedReciprocalBlockSum_264, roundedReciprocalBlockSum_265, roundedReciprocalBlockSum_266, roundedReciprocalBlockSum_267, roundedReciprocalBlockSum_268, roundedReciprocalBlockSum_269, roundedReciprocalBlockSum_270]
    _ = 3052837 := by norm_num

end PrimeFactorUnimodality
