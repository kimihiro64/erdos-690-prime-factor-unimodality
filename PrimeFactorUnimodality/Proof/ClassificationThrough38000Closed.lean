import PrimeFactorUnimodality.Proof.ClassificationThrough38000
import PrimeFactorUnimodality.Proof.LargeRange.RecordTwinClosed

set_option autoImplicit false

/-!
# Closed classification through 38,000

This module consumes the kernel-replayed record twin certificate and removes
the last hypothesis from the finite-range classification.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The exact density classification through `k = 38,000`, with the record
twin-prime input discharged by its closed certificate. -/
theorem completeClassification_through38000_closed
    (k : Nat) (hk : 1 ≤ k) (hkUpper : k ≤ 38000) :
    IsUnimodal (primeFactorDensity k) ↔ k ≤ 3 :=
  completeClassification_through38000 recordTwin_consecutive k hk hkUpper

end

end PrimeFactorUnimodality
