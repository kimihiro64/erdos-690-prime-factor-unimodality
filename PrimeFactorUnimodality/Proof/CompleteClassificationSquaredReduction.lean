import PrimeFactorUnimodality.Helpers.Analytic.DusartPublishedPrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.DusartPublishedShortInterval
import PrimeFactorUnimodality.Helpers.Analytic.DusartPublishedTailTheta
import PrimeFactorUnimodality.Proof.CompleteClassificationReduction

set_option autoImplicit false

/-! # The exact all-k classification from one theta-error ray

The three tail requirements follow from one log-square theta error. All three
bounded prefixes through 3,594,641 and the endpoint prime count are checked;
the same theta estimate implies both Abel anchors. No bounded analytic premise
remains. The finite classification and unbounded theta estimate remain explicit.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The only unbounded analytic premise is the shared theta-error ray.
The finite classification has precisely the existing cutoff 38,000. -/
theorem completeClassification_of_squaredTheta_and_finite_range
    (finiteRange : ∀ k : Nat, 1 ≤ k → k ≤ 38000 →
      (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3))
    (error : HasThetaLogSquaredError (1 / 5) 3594641) : CompleteClassification := by
  have primeCounting := hasDusartPrimeCountingBounds_of_logSquared_ray error
  exact completeClassification_of_finite_prefix_and_tailTheta finiteRange primeCounting
    (hasTailThetaBounds_of_logSquared_ray error)
    (hasUniformTailPrimePair_of_shortInterval
      (hasDusartShortIntervalPrime_of_logSquared_ray error))

end

end PrimeFactorUnimodality
