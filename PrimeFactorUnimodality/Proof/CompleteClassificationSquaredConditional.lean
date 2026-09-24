import PrimeFactorUnimodality.Proof.ClassificationThrough38000Closed
import PrimeFactorUnimodality.Proof.CompleteClassificationSquaredReduction

set_option autoImplicit false

/-! # The all-k classification conditional on one unbounded theta estimate

The finite classification uses the actual record-twin certificate. All finite
analytic prefixes and Abel anchors are discharged by their proved providers.
The sole premise is the log-square theta-error ray from its published cutoff;
it is an explicit theorem parameter, not an additional axiom.
-/

namespace PrimeFactorUnimodality

theorem completeClassification_assuming_theta_error
    (error : HasThetaLogSquaredError (1 / 5) 3594641) : CompleteClassification :=
  completeClassification_of_squaredTheta_and_finite_range
    (completeClassification_through38000_of_primeCounting
      (hasDusartPrimeCountingBounds_of_logSquared_ray error)) error

end PrimeFactorUnimodality
