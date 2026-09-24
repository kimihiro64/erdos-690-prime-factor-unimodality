import PrimeFactorUnimodality.Proof.CompleteClassificationSquaredReduction

/-! Check the exact prime-count endpoint and the reduced all-k input boundary. -/

open PrimeFactorUnimodality

example : Nat.primeCounting 3594641 = 256357 := dusart_published_prime_count

example : HasDusartRealPrimeCountingBoundsBelow 3594641 :=
  dusart_published_primeCountingPrefix

example (error : HasThetaLogSquaredError (1 / 5) 3594641) : HasDusartPrimeCountingBounds :=
  hasDusartPrimeCountingBounds_of_logSquared_ray error

example : HasDusartShortIntervalPrimeBelow 3594641 := dusart_published_shortIntervalPrefix

example (error : HasThetaLogSquaredError (1 / 5) 3594641) : HasDusartShortIntervalPrime :=
  hasDusartShortIntervalPrime_of_logSquared_ray error

example (q : Nat) (hq : 3501 ≤ q) (hcut : q < 3594641) : TailThetaAt q :=
  dusart_tail_theta_prefix q hq hcut

example (error : HasThetaLogSquaredError (1 / 5) 3594641) : HasTailThetaBounds :=
  hasTailThetaBounds_of_logSquared_ray error

example (finiteRange : ∀ k : Nat, 1 ≤ k → k ≤ 38000 →
      (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3))
    (error : HasThetaLogSquaredError (1 / 5) 3594641) :
    ∀ k : Nat, 1 ≤ k → (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3) :=
  completeClassification_of_squaredTheta_and_finite_range finiteRange error
