import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums.Part10


/-! Generated fixed-point reciprocal-weight certificates, segment 11. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt24250 :
    fixedWeightSums 1000000000 24250 = (3347832302, 3347835000) := by
  rw [show 24250 = 24000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt24000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt24500 :
    fixedWeightSums 1000000000 24500 = (3348652254, 3348654972) := by
  rw [show 24500 = 24250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt24250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt24750 :
    fixedWeightSums 1000000000 24750 = (3349464499, 3349467237) := by
  rw [show 24750 = 24500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt24500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt25000 :
    fixedWeightSums 1000000000 25000 = (3350429129, 3350431891) := by
  rw [show 25000 = 24750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt24750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt25250 :
    fixedWeightSums 1000000000 25250 = (3351383982, 3351386768) := by
  rw [show 25250 = 25000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt25000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt25500 :
    fixedWeightSums 1000000000 25500 = (3352329801, 3352332611) := by
  rw [show 25500 = 25250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt25250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt25750 :
    fixedWeightSums 1000000000 25750 = (3353305102, 3353307937) := by
  rw [show 25750 = 25500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt25500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt26000 :
    fixedWeightSums 1000000000 26000 = (3354271056, 3354273916) := by
  rw [show 26000 = 25750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt25750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt26250 :
    fixedWeightSums 1000000000 26250 = (3355189606, 3355192490) := by
  rw [show 26250 = 26000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt26000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt26500 :
    fixedWeightSums 1000000000 26500 = (3356175549, 3356178459) := by
  rw [show 26500 = 26250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt26250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

end PrimeFactorUnimodality
