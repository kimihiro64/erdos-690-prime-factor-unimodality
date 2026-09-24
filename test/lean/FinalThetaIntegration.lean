import PrimeFactorUnimodality.Helpers.FiniteCertificates.DusartReflectedBootstrap
import PrimeFactorUnimodality.Proof.CompleteClassificationSquaredReduction

/-! The actual Dusart reductions must coexist with the Mertens-based all-k reduction. -/

open PrimeFactorUnimodality

example
    (finiteRange : ∀ k : Nat, 1 ≤ k → k ≤ 38000 →
      (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3))
    (finiteTheta : ∀ x : Real, (3594641 : Real) ≤ x → x ≤ 3000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : Real) * x / Real.log x ^ 2)
    (lowZeros : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : Real)) : CompleteClassification :=
  completeClassification_of_squaredTheta_and_finite_range finiteRange
    (hasThetaLogSquaredError_of_lower_band_and_verified_low finiteTheta lowZeros)
