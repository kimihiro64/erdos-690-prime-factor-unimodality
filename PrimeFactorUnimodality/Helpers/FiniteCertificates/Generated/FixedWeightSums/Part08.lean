import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums.Part07


/-! Generated fixed-point reciprocal-weight certificates, segment 8. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt16750 :
    fixedWeightSums 1000000000 16750 = (3310295024, 3310296960) := by
  rw [show 16750 = 16500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt16500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt17000 :
    fixedWeightSums 1000000000 17000 = (3311716167, 3311718127) := by
  rw [show 17000 = 16750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt16750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt17250 :
    fixedWeightSums 1000000000 17250 = (3313176570, 3313178555) := by
  rw [show 17250 = 17000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt17000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt17500 :
    fixedWeightSums 1000000000 17500 = (3314844159, 3314846173) := by
  rw [show 17500 = 17250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt17250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt17750 :
    fixedWeightSums 1000000000 17750 = (3316205287, 3316207325) := by
  rw [show 17750 = 17500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt17500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt18000 :
    fixedWeightSums 1000000000 18000 = (3317658589, 3317660653) := by
  rw [show 18000 = 17750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt17750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt18250 :
    fixedWeightSums 1000000000 18250 = (3319092845, 3319094935) := by
  rw [show 18250 = 18000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt18000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt18500 :
    fixedWeightSums 1000000000 18500 = (3320617415, 3320619533) := by
  rw [show 18500 = 18250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt18250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt18750 :
    fixedWeightSums 1000000000 18750 = (3321798634, 3321800774) := by
  rw [show 18750 = 18500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt18500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt19000 :
    fixedWeightSums 1000000000 19000 = (3322752489, 3322754647) := by
  rw [show 19000 = 18750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt18750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

end PrimeFactorUnimodality
