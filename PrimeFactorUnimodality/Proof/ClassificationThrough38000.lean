import PrimeFactorUnimodality.Proof.ClassificationThrough48
import PrimeFactorUnimodality.Proof.LargeRange.RecordRange

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-! The complete classification through the closed record-input cutoff,
from the record-twin certificate and the prime-counting input also used by
the infinite tail. -/
theorem completeClassification_through38000
    (bounds : HasDusartPrimeCountingBounds)
    (twin : ConsecutivePrimes recordLower recordUpper)
    (k : Nat) (hk : 1 ≤ k) (hkUpper : k ≤ 38000) :
    IsUnimodal (primeFactorDensity k) ↔ k ≤ 3 := by
  by_cases hk48 : k ≤ 48
  · exact completeClassification_through48 k hk hk48
  · constructor
    · intro unimodal
      exact False.elim
        ((recordRange_not_isUnimodal bounds twin k (by omega) hkUpper) unimodal)
    · intro hk3
      omega

end

end PrimeFactorUnimodality
