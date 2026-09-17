import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums.Part09


/-! Generated fixed-point reciprocal-weight certificates, segment 10. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt21750 :
    fixedWeightSums 1000000000 21750 = (3336567650, 3336570089) := by
  rw [show 21750 = 21500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt21500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt22000 :
    fixedWeightSums 1000000000 22000 = (3337711095, 3337713559) := by
  rw [show 22000 = 21750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt21750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt22250 :
    fixedWeightSums 1000000000 22250 = (3338932421, 3338934912) := by
  rw [show 22250 = 22000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt22000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt22500 :
    fixedWeightSums 1000000000 22500 = (3340005581, 3340008096) := by
  rw [show 22500 = 22250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt22250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt22750 :
    fixedWeightSums 1000000000 22750 = (3341198566, 3341201108) := by
  rw [show 22750 = 22500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt22500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt23000 :
    fixedWeightSums 1000000000 23000 = (3342160602, 3342163166) := by
  rw [show 23000 = 22750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt22750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt23250 :
    fixedWeightSums 1000000000 23250 = (3343372634, 3343375226) := by
  rw [show 23250 = 23000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt23000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt23500 :
    fixedWeightSums 1000000000 23500 = (3344271695, 3344274308) := by
  rw [show 23500 = 23250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt23250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt23750 :
    fixedWeightSums 1000000000 23750 = (3345457078, 3345459719) := by
  rw [show 23750 = 23500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt23500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt24000 :
    fixedWeightSums 1000000000 24000 = (3346588288, 3346590956) := by
  rw [show 24000 = 23750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt23750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

end PrimeFactorUnimodality
