import Submission.Internal.PrimeFactorUnimodality.Proof.CompleteClassificationElementary

namespace Submission.Internal

set_option autoImplicit false

/-! # Unconditional all-k Erdos 690 solution

The theorem uses elementary analytic estimates and the existing fixed witnesses.
-/

theorem PrimeFactorUnimodality.completeClassification :
    PrimeFactorUnimodality.CompleteClassification := by
  exact PrimeFactorUnimodality.completeClassification_elementary

end Submission.Internal
