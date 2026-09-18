import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part051
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part052
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part053
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part054
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part055
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part056
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part057
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part058
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part059
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part060

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 006. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_006 :
    roundedReciprocalBlockSum 50000 60000 = 16841493 := by
  calc
    roundedReciprocalBlockSum 50000 60000 =
        roundedReciprocalBlockSum 50000 51000 +
          roundedReciprocalBlockSum 51000 52000 + roundedReciprocalBlockSum 52000 53000 + roundedReciprocalBlockSum 53000 54000 + roundedReciprocalBlockSum 54000 55000 + roundedReciprocalBlockSum 55000 56000 + roundedReciprocalBlockSum 56000 57000 + roundedReciprocalBlockSum 57000 58000 + roundedReciprocalBlockSum 58000 59000 + roundedReciprocalBlockSum 59000 60000 := by
      rw [roundedReciprocalBlockSum_add_block (show 50000 ≤ 59000 by omega) (show 59000 ≤ 60000 by omega), roundedReciprocalBlockSum_add_block (show 50000 ≤ 58000 by omega) (show 58000 ≤ 59000 by omega), roundedReciprocalBlockSum_add_block (show 50000 ≤ 57000 by omega) (show 57000 ≤ 58000 by omega), roundedReciprocalBlockSum_add_block (show 50000 ≤ 56000 by omega) (show 56000 ≤ 57000 by omega), roundedReciprocalBlockSum_add_block (show 50000 ≤ 55000 by omega) (show 55000 ≤ 56000 by omega), roundedReciprocalBlockSum_add_block (show 50000 ≤ 54000 by omega) (show 54000 ≤ 55000 by omega), roundedReciprocalBlockSum_add_block (show 50000 ≤ 53000 by omega) (show 53000 ≤ 54000 by omega), roundedReciprocalBlockSum_add_block (show 50000 ≤ 52000 by omega) (show 52000 ≤ 53000 by omega), roundedReciprocalBlockSum_add_block (show 50000 ≤ 51000 by omega) (show 51000 ≤ 52000 by omega)]
    _ = 1763037 + 1883187 + 1694883 + 1719648 + 1651416 + 1675185 + 1751383 + 1582673 + 1539091 + 1580990 := by
      rw [roundedReciprocalBlockSum_051, roundedReciprocalBlockSum_052, roundedReciprocalBlockSum_053, roundedReciprocalBlockSum_054, roundedReciprocalBlockSum_055, roundedReciprocalBlockSum_056, roundedReciprocalBlockSum_057, roundedReciprocalBlockSum_058, roundedReciprocalBlockSum_059, roundedReciprocalBlockSum_060]
    _ = 16841493 := by norm_num

end PrimeFactorUnimodality
