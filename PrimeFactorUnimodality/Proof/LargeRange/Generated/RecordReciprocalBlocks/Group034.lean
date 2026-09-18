import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part331
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part332
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part333
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part334
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part335
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part336
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part337
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part338
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part339
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part340

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 034. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_034 :
    roundedReciprocalBlockSum 330000 340000 = 2424922 := by
  calc
    roundedReciprocalBlockSum 330000 340000 =
        roundedReciprocalBlockSum 330000 331000 +
          roundedReciprocalBlockSum 331000 332000 + roundedReciprocalBlockSum 332000 333000 + roundedReciprocalBlockSum 333000 334000 + roundedReciprocalBlockSum 334000 335000 + roundedReciprocalBlockSum 335000 336000 + roundedReciprocalBlockSum 336000 337000 + roundedReciprocalBlockSum 337000 338000 + roundedReciprocalBlockSum 338000 339000 + roundedReciprocalBlockSum 339000 340000 := by
      rw [roundedReciprocalBlockSum_add_block (show 330000 ≤ 339000 by omega) (show 339000 ≤ 340000 by omega), roundedReciprocalBlockSum_add_block (show 330000 ≤ 338000 by omega) (show 338000 ≤ 339000 by omega), roundedReciprocalBlockSum_add_block (show 330000 ≤ 337000 by omega) (show 337000 ≤ 338000 by omega), roundedReciprocalBlockSum_add_block (show 330000 ≤ 336000 by omega) (show 336000 ≤ 337000 by omega), roundedReciprocalBlockSum_add_block (show 330000 ≤ 335000 by omega) (show 335000 ≤ 336000 by omega), roundedReciprocalBlockSum_add_block (show 330000 ≤ 334000 by omega) (show 334000 ≤ 335000 by omega), roundedReciprocalBlockSum_add_block (show 330000 ≤ 333000 by omega) (show 333000 ≤ 334000 by omega), roundedReciprocalBlockSum_add_block (show 330000 ≤ 332000 by omega) (show 332000 ≤ 333000 by omega), roundedReciprocalBlockSum_add_block (show 330000 ≤ 331000 by omega) (show 331000 ≤ 332000 by omega)]
    _ = 251197 + 253428 + 228618 + 254913 + 239201 + 244483 + 255605 + 248926 + 248217 + 200334 := by
      rw [roundedReciprocalBlockSum_331, roundedReciprocalBlockSum_332, roundedReciprocalBlockSum_333, roundedReciprocalBlockSum_334, roundedReciprocalBlockSum_335, roundedReciprocalBlockSum_336, roundedReciprocalBlockSum_337, roundedReciprocalBlockSum_338, roundedReciprocalBlockSum_339, roundedReciprocalBlockSum_340]
    _ = 2424922 := by norm_num

end PrimeFactorUnimodality
