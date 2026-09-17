import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums.Part13


/-! Generated fixed-point reciprocal-weight certificates, segment 14. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt31469 :
    fixedWeightSums 1000000000 31469 = (3372614478, 3372617863) := by
  rw [show 31469 = 31397 + 72 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt31397]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

end PrimeFactorUnimodality
