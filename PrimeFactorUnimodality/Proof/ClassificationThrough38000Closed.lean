import PrimeFactorUnimodality.Proof.ClassificationThrough38000
import PrimeFactorUnimodality.Proof.LargeRange.RecordTwinClosed

set_option autoImplicit false

/-!
# Classification through 38,000 with the twin certificate discharged

This module consumes the kernel-replayed record twin certificate. The
prime-counting input is shared with the infinite tail; no separate 38,000-prime
witness list is needed.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The exact density classification through `k = 38,000`, with the record
twin-prime input discharged by its closed certificate. -/
theorem completeClassification_through38000_of_primeCounting
    (bounds : HasDusartPrimeCountingBounds)
    (k : Nat) (hk : 1 ≤ k) (hkUpper : k ≤ 38000) :
    IsUnimodal (primeFactorDensity k) ↔ k ≤ 3 :=
  completeClassification_through38000 bounds recordTwin_consecutive k hk hkUpper

end

end PrimeFactorUnimodality
