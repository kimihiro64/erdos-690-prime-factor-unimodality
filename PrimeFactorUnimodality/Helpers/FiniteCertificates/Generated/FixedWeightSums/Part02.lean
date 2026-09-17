import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums.Part01


/-! Generated fixed-point reciprocal-weight certificates, segment 2. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt2250 :
    fixedWeightSums 1000000000 2250 = (3080194944, 3080195278) := by
  rw [show 2250 = 2000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt2000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt2500 :
    fixedWeightSums 1000000000 2500 = (3094164212, 3094164579) := by
  rw [show 2500 = 2250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt2250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt2750 :
    fixedWeightSums 1000000000 2750 = (3107057107, 3107057508) := by
  rw [show 2750 = 2500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt2500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt3000 :
    fixedWeightSums 1000000000 3000 = (3117168769, 3117169199) := by
  rw [show 3000 = 2750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt2750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt3250 :
    fixedWeightSums 1000000000 3250 = (3125835883, 3125836340) := by
  rw [show 3250 = 3000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt3000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt3500 :
    fixedWeightSums 1000000000 3500 = (3135346307, 3135346796) := by
  rw [show 3500 = 3250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt3250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt3750 :
    fixedWeightSums 1000000000 3750 = (3144468663, 3144469185) := by
  rw [show 3750 = 3500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt3500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt4000 :
    fixedWeightSums 1000000000 4000 = (3151712365, 3151712915) := by
  rw [show 4000 = 3750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt3750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt4250 :
    fixedWeightSums 1000000000 4250 = (3159488755, 3159489337) := by
  rw [show 4250 = 4000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt4000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt4500 :
    fixedWeightSums 1000000000 4500 = (3165898022, 3165898632) := by
  rw [show 4500 = 4250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt4250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

end PrimeFactorUnimodality
