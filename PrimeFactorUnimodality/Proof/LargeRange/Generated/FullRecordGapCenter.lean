import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenterValue
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapStructure

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option exponentiation.threshold 100000
set_option linter.style.longLine false

/-! Literal bridge for the published full record-gap center. -/

namespace PrimeFactorUnimodality

set_option maxHeartbeats 0 in
-- Exact reduction of the 4,499-factor center is intentionally unbounded.
theorem recordGapCenter_eq_fullRecordGapCenterValue :
    recordGapCenter = fullRecordGapCenterValue := by
  rfl

end PrimeFactorUnimodality
