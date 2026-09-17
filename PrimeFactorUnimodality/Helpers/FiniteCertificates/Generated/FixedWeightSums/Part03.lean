import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums.Part02


/-! Generated fixed-point reciprocal-weight certificates, segment 3. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt4750 :
    fixedWeightSums 1000000000 4750 = (3172177465, 3172178104) := by
  rw [show 4750 = 4500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt4500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt5000 :
    fixedWeightSums 1000000000 5000 = (3178323926, 3178324595) := by
  rw [show 5000 = 4750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt4750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt5250 :
    fixedWeightSums 1000000000 5250 = (3183795661, 3183796358) := by
  rw [show 5250 = 5000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt5000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt5500 :
    fixedWeightSums 1000000000 5500 = (3189000407, 3189001132) := by
  rw [show 5500 = 5250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt5250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt5750 :
    fixedWeightSums 1000000000 5750 = (3194689950, 3194690707) := by
  rw [show 5750 = 5500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt5500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt6000 :
    fixedWeightSums 1000000000 6000 = (3199123092, 3199123875) := by
  rw [show 6000 = 5750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt5750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt6250 :
    fixedWeightSums 1000000000 6250 = (3203860406, 3203861218) := by
  rw [show 6250 = 6000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt6000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt6500 :
    fixedWeightSums 1000000000 6500 = (3208578087, 3208578929) := by
  rw [show 6500 = 6250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt6250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt6750 :
    fixedWeightSums 1000000000 6750 = (3212651024, 3212651893) := by
  rw [show 6750 = 6500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt6500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt7000 :
    fixedWeightSums 1000000000 7000 = (3217157514, 3217158414) := by
  rw [show 7000 = 6750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt6750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

end PrimeFactorUnimodality
