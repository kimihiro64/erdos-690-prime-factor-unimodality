import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part071
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part072
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part073
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part074
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part075
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part076
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part077
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part078
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part079
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part080

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 008. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_008 :
    roundedReciprocalBlockSum 70000 80000 = 12054669 := by
  calc
    roundedReciprocalBlockSum 70000 80000 =
        roundedReciprocalBlockSum 70000 71000 +
          roundedReciprocalBlockSum 71000 72000 + roundedReciprocalBlockSum 72000 73000 + roundedReciprocalBlockSum 73000 74000 + roundedReciprocalBlockSum 74000 75000 + roundedReciprocalBlockSum 75000 76000 + roundedReciprocalBlockSum 76000 77000 + roundedReciprocalBlockSum 77000 78000 + roundedReciprocalBlockSum 78000 79000 + roundedReciprocalBlockSum 79000 80000 := by
      rw [roundedReciprocalBlockSum_add_block (show 70000 ≤ 79000 by omega) (show 79000 ≤ 80000 by omega), roundedReciprocalBlockSum_add_block (show 70000 ≤ 78000 by omega) (show 78000 ≤ 79000 by omega), roundedReciprocalBlockSum_add_block (show 70000 ≤ 77000 by omega) (show 77000 ≤ 78000 by omega), roundedReciprocalBlockSum_add_block (show 70000 ≤ 76000 by omega) (show 76000 ≤ 77000 by omega), roundedReciprocalBlockSum_add_block (show 70000 ≤ 75000 by omega) (show 75000 ≤ 76000 by omega), roundedReciprocalBlockSum_add_block (show 70000 ≤ 74000 by omega) (show 74000 ≤ 75000 by omega), roundedReciprocalBlockSum_add_block (show 70000 ≤ 73000 by omega) (show 73000 ≤ 74000 by omega), roundedReciprocalBlockSum_add_block (show 70000 ≤ 72000 by omega) (show 72000 ≤ 73000 by omega), roundedReciprocalBlockSum_add_block (show 70000 ≤ 71000 by omega) (show 71000 ≤ 72000 by omega)]
    _ = 1390140 + 1328402 + 1241222 + 1129197 + 1235116 + 1205280 + 1085001 + 1225920 + 1070078 + 1144313 := by
      rw [roundedReciprocalBlockSum_071, roundedReciprocalBlockSum_072, roundedReciprocalBlockSum_073, roundedReciprocalBlockSum_074, roundedReciprocalBlockSum_075, roundedReciprocalBlockSum_076, roundedReciprocalBlockSum_077, roundedReciprocalBlockSum_078, roundedReciprocalBlockSum_079, roundedReciprocalBlockSum_080]
    _ = 12054669 := by norm_num

end PrimeFactorUnimodality
