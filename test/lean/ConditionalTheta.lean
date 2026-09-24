import PrimeFactorUnimodality.Proof.CompleteClassificationSquaredConditional

/-! The strengthened conditional boundary has exactly one analytic premise and retains every k. -/

open PrimeFactorUnimodality

example (error : HasThetaLogSquaredError (1 / 5) 3594641) :
    ∀ k : Nat, 1 ≤ k → (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3) :=
  completeClassification_assuming_theta_error error
