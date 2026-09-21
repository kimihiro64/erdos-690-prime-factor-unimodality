import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapOwnerRows

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

/-! Shared generated archive-row structure. -/

namespace PrimeFactorUnimodality

structure FullRecordGapArchiveRow where
  d : Nat
  q : Nat
  r : Nat

end PrimeFactorUnimodality
