import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks.Part501

set_option autoImplicit false

/-! Assembly of reciprocal wheel-sieve certificate group 051. -/

namespace PrimeFactorUnimodality

theorem roundedReciprocalGroup_051 :
    roundedReciprocalBlockSum 500000 500001 = 0 := by
  calc
    roundedReciprocalBlockSum 500000 500001 =
        roundedReciprocalBlockSum 500000 500001 +
           := by
      rw []
    _ = 0 := by
      rw [roundedReciprocalBlockSum_501]
    _ = 0 := by norm_num

end PrimeFactorUnimodality
