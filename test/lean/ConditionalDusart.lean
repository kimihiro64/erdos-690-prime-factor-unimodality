import PrimeFactorUnimodality.Proof.CompleteClassificationConditional

/-! The conditional boundary retains every k and exactly three analytic inputs. -/

open PrimeFactorUnimodality

example (primeCounting : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (shortInterval : HasDusartShortIntervalPrime) :
    ∀ k : Nat, 1 ≤ k → (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3) :=
  completeClassification_assuming_dusart primeCounting thetaBounds shortInterval
