import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums.Part06


/-! Generated fixed-point reciprocal-weight certificates, segment 7. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt14750 :
    fixedWeightSums 1000000000 14750 = (3296985776, 3296987503) := by
  rw [show 14750 = 14500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt14500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt15000 :
    fixedWeightSums 1000000000 15000 = (3298802599, 3298804353) := by
  rw [show 15000 = 14750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt14750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt15250 :
    fixedWeightSums 1000000000 15250 = (3300455230, 3300457009) := by
  rw [show 15250 = 15000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt15000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt15500 :
    fixedWeightSums 1000000000 15500 = (3302472729, 3302474539) := by
  rw [show 15500 = 15250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt15250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt15683 :
    fixedWeightSums 1000000000 15683 = (3303754306, 3303756136) := by
  rw [show 15683 = 15500 + 183 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt15500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt15727 :
    fixedWeightSums 1000000000 15727 = (3303818073, 3303819904) := by
  rw [show 15727 = 15683 + 44 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt15683]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt15750 :
    fixedWeightSums 1000000000 15750 = (3304199385, 3304201222) := by
  rw [show 15750 = 15727 + 23 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt15727]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt16000 :
    fixedWeightSums 1000000000 16000 = (3305774944, 3305776806) := by
  rw [show 16000 = 15750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt15750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt16250 :
    fixedWeightSums 1000000000 16250 = (3307387553, 3307389441) := by
  rw [show 16250 = 16000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt16000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt16500 :
    fixedWeightSums 1000000000 16500 = (3308852168, 3308854080) := by
  rw [show 16500 = 16250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt16250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

end PrimeFactorUnimodality
