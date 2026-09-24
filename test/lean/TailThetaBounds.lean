import PrimeFactorUnimodality.Proof.CompleteClassificationReduction

/-! Regression checks for the weaker theta boundary and its exact all-k consumer.
The finite prefix and remaining analytic inputs are explicit parameters here.
-/

open PrimeFactorUnimodality

example (bounds : HasDusartThetaBounds) : HasTailThetaBounds :=
  hasTailThetaBounds_of_dusart bounds

example (error : HasThetaLogSquaredError (1 / 5) 3594641) : TailThetaAt 3594641 :=
  tailThetaAt_of_logSquared error (by decide)

example (finiteRange : ∀ k : Nat, 1 ≤ k → k ≤ 38000 →
      (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3))
    (primeCounting : HasDusartPrimeCountingBounds)
    (thetaPrefix : ∀ q : Nat, 3501 ≤ q → q < 3594641 → TailThetaAt q)
    (thetaError : HasThetaLogSquaredError (1 / 5) 3594641)
    (shortInterval : HasDusartShortIntervalPrime) :
    ∀ k : Nat, 1 ≤ k → (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3) :=
  completeClassification_of_finite_prefix_and_logSquared finiteRange primeCounting
    thetaPrefix thetaError shortInterval
