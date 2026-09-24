import PrimeFactorUnimodality.Helpers.Analytic.DusartSquaredAtPublishedCutoff
import PrimeFactorUnimodality.Proof.CompleteClassificationReduction

set_option autoImplicit false

/-! # The exact all-k classification from one theta-error ray

The three tail requirements follow from one log-square theta error, bounded
prefixes through 3,594,641, and the two Abel anchor comparisons at that point.
The stronger Dusart theta upper theorem is not a premise. All finite inputs
and the remaining unbounded theta estimate are explicit theorem parameters;
this module does not provide their proofs or generate their numerical data.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Complete bounded input boundary for the shared log-square analytic ray.
The two anchors are stated without rounding or implicit endpoint margins. -/
structure SquaredThetaFiniteInputs : Prop where
  primeCounting : HasDusartRealPrimeCountingBoundsBelow 3594641
  shortInterval : HasDusartShortIntervalPrimeBelow 3594641
  theta : ∀ q : Nat, 3501 ≤ q → q < 3594641 → TailThetaAt q
  lowerAnchor : Chebyshev.theta 3594641 * Real.log 3594641 ^ 2 +
    3594641 * Real.log 3594641 + (1 / 5 : Real) * 3594641 ≤
      (Nat.primeCounting 3594641 : Real) * Real.log 3594641 ^ 3
  upperAnchor : (Nat.primeCounting 3594641 : Real) * Real.log 3594641 ^ 3 ≤
    Chebyshev.theta 3594641 * Real.log 3594641 ^ 2 +
      (6381 / 5000 : Real) * 3594641 * Real.log 3594641 - (1 / 5 : Real) * 3594641

/-- The only unbounded analytic premise is the shared theta-error ray.
The finite classification has precisely the existing cutoff 38,000. -/
theorem completeClassification_of_squaredTheta_and_finite_inputs
    (finiteRange : ∀ k : Nat, 1 ≤ k → k ≤ 38000 →
      (IsUnimodal (primeFactorDensity k) ↔ k ≤ 3))
    (finite : SquaredThetaFiniteInputs)
    (error : HasThetaLogSquaredError (1 / 5) 3594641) : CompleteClassification := by
  have primeCounting := hasDusartPrimeCountingBounds_of_published_logSquared
    finite.primeCounting error finite.lowerAnchor finite.upperAnchor
  exact completeClassification_of_finite_prefix_and_logSquared finiteRange primeCounting
    finite.theta error
    (hasDusartShortIntervalPrime_of_published_logSquared finite.shortInterval error)

end

end PrimeFactorUnimodality
