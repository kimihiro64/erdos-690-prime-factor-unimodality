import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums.Part11


/-! Generated fixed-point reciprocal-weight certificates, segment 12. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt26750 :
    fixedWeightSums 1000000000 26750 = (3357151254, 3357154190) := by
  rw [show 26750 = 26500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt26500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt27000 :
    fixedWeightSums 1000000000 27000 = (3358081251, 3358084212) := by
  rw [show 27000 = 26750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt26750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt27250 :
    fixedWeightSums 1000000000 27250 = (3358855806, 3358858788) := by
  rw [show 27250 = 27000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt27000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt27500 :
    fixedWeightSums 1000000000 27500 = (3359659579, 3359662583) := by
  rw [show 27500 = 27250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt27250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt27750 :
    fixedWeightSums 1000000000 27750 = (3360491796, 3360494823) := by
  rw [show 27750 = 27500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt27500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt28000 :
    fixedWeightSums 1000000000 28000 = (3361496698, 3361499753) := by
  rw [show 28000 = 27750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt27750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt28250 :
    fixedWeightSums 1000000000 28250 = (3362279257, 3362282334) := by
  rw [show 28250 = 28000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt28000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt28500 :
    fixedWeightSums 1000000000 28500 = (3363089706, 3363092806) := by
  rw [show 28500 = 28250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt28250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt28750 :
    fixedWeightSums 1000000000 28750 = (3364137983, 3364141113) := by
  rw [show 28750 = 28500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt28500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt29000 :
    fixedWeightSums 1000000000 29000 = (3364935061, 3364938214) := by
  rw [show 29000 = 28750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt28750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

end PrimeFactorUnimodality
