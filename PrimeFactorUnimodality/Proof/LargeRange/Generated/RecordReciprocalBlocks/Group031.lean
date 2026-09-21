import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Group030
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part310

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 031. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_031 :
    roundedReciprocalBlockSum 300000 310000 = 2696232 := by
  calc
    roundedReciprocalBlockSum 300000 310000 =
        roundedReciprocalBlockSum 300000 301000 +
          roundedReciprocalBlockSum 301000 302000 + roundedReciprocalBlockSum 302000 303000 + roundedReciprocalBlockSum 303000 304000 + roundedReciprocalBlockSum 304000 305000 + roundedReciprocalBlockSum 305000 306000 + roundedReciprocalBlockSum 306000 307000 + roundedReciprocalBlockSum 307000 308000 + roundedReciprocalBlockSum 308000 309000 + roundedReciprocalBlockSum 309000 310000 := by
      rw [roundedReciprocalBlockSum_add_block (show 300000 ≤ 309000 by omega) (show 309000 ≤ 310000 by omega), roundedReciprocalBlockSum_add_block (show 300000 ≤ 308000 by omega) (show 308000 ≤ 309000 by omega), roundedReciprocalBlockSum_add_block (show 300000 ≤ 307000 by omega) (show 307000 ≤ 308000 by omega), roundedReciprocalBlockSum_add_block (show 300000 ≤ 306000 by omega) (show 306000 ≤ 307000 by omega), roundedReciprocalBlockSum_add_block (show 300000 ≤ 305000 by omega) (show 305000 ≤ 306000 by omega), roundedReciprocalBlockSum_add_block (show 300000 ≤ 304000 by omega) (show 304000 ≤ 305000 by omega), roundedReciprocalBlockSum_add_block (show 300000 ≤ 303000 by omega) (show 303000 ≤ 304000 by omega), roundedReciprocalBlockSum_add_block (show 300000 ≤ 302000 by omega) (show 302000 ≤ 303000 by omega), roundedReciprocalBlockSum_add_block (show 300000 ≤ 301000 by omega) (show 301000 ≤ 302000 by omega)]
    _ = 286206 + 288572 + 241303 + 276828 + 298883 + 271733 + 267570 + 247227 + 259354 + 258556 := by
      rw [roundedReciprocalBlockSum_301, roundedReciprocalBlockSum_302, roundedReciprocalBlockSum_303, roundedReciprocalBlockSum_304, roundedReciprocalBlockSum_305, roundedReciprocalBlockSum_306, roundedReciprocalBlockSum_307, roundedReciprocalBlockSum_308, roundedReciprocalBlockSum_309, roundedReciprocalBlockSum_310]
    _ = 2696232 := by norm_num

end PrimeFactorUnimodality
