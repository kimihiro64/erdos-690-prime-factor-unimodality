import PrimeFactorUnimodality.Helpers.Analytic.DusartPublishedAnchors
import PrimeFactorUnimodality.Helpers.FiniteCertificates.DusartPublishedPrimeCount
import PrimeFactorUnimodality.Proof.CompleteClassificationReduction

set_option autoImplicit false

/-! # The exact all-k classification from one theta-error ray

The three tail requirements follow from one log-square theta error and bounded
prefixes through 3,594,641. The exact endpoint prime count is checked separately;
the same theta estimate then implies both Abel anchor comparisons. The stronger
Dusart theta upper theorem is not a premise. The remaining finite prefixes and
unbounded theta estimate are explicit inputs, not supplied by this module.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The three bounded prefixes left after discharging the endpoint count and
deriving both Abel anchors from the shared theta-error hypothesis. -/
structure SquaredThetaFiniteInputs : Prop where
  primeCounting : HasDusartRealPrimeCountingBoundsBelow 3594641
  shortInterval : HasDusartShortIntervalPrimeBelow 3594641
  theta : ∀ q : Nat, 3501 ≤ q → q < 3594641 → TailThetaAt q

/-- The only unbounded analytic premise is the shared theta-error ray.
The finite classification has precisely the existing cutoff 38,000. -/
theorem completeClassification_of_squaredTheta_and_finite_inputs
    (finiteRange : ∀ k : Nat, 1 ≤ k → k ≤ 38000 →
      (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3))
    (finite : SquaredThetaFiniteInputs)
    (error : HasThetaLogSquaredError (1 / 5) 3594641) : CompleteClassification := by
  have primeCounting := hasDusartPrimeCountingBounds_of_published_logSquared_count
    dusart_published_prime_count finite.primeCounting error
  exact completeClassification_of_finite_prefix_and_logSquared finiteRange primeCounting
    finite.theta error
    (hasDusartShortIntervalPrime_of_published_logSquared finite.shortInterval error)

end

end PrimeFactorUnimodality
