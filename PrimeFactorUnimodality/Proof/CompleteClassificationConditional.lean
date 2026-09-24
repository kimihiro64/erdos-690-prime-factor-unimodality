import PrimeFactorUnimodality.Proof.ClassificationThrough38000Closed
import PrimeFactorUnimodality.Proof.CompleteClassificationReduction

/-! # The full classification conditional only on the three Dusart inputs

This independent build target checks the finite certificates and the infinite
CRT argument without importing the unfinished analytic providers. Its three
hypotheses are explicit theorem parameters, not additional axioms. The target
does not replace the unconditional Challenge or Solution.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- For every positive k, unimodality holds exactly through three, assuming
the prime-counting, theta and short-interval bounds used by the paper. -/
theorem completeClassification_assuming_dusart
    (primeCounting : HasDusartPrimeCountingBounds)
    (thetaBounds : HasDusartThetaBounds)
    (shortInterval : HasDusartShortIntervalPrime) : CompleteClassification := by
  exact completeClassification_of_finite_prefix_and_primeCounting
    (completeClassification_through38000_of_primeCounting primeCounting)
    primeCounting thetaBounds (hasUniformTailPrimePair_of_shortInterval shortInterval)

end

end PrimeFactorUnimodality
