import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums.Part03


/-! Generated fixed-point reciprocal-weight certificates, segment 4. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt7250 :
    fixedWeightSums 1000000000 7250 = (3220943363, 3220944290) := by
  rw [show 7250 = 7000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt7000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt7500 :
    fixedWeightSums 1000000000 7500 = (3224056649, 3224057599) := by
  rw [show 7500 = 7250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt7250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt7750 :
    fixedWeightSums 1000000000 7750 = (3228258468, 3228259450) := by
  rw [show 7750 = 7500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt7500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt8000 :
    fixedWeightSums 1000000000 8000 = (3231435341, 3231436348) := by
  rw [show 8000 = 7750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt7750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt8250 :
    fixedWeightSums 1000000000 8250 = (3234879644, 3234880679) := by
  rw [show 8250 = 8000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt8000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt8500 :
    fixedWeightSums 1000000000 8500 = (3237750281, 3237751340) := by
  rw [show 8500 = 8250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt8250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt8750 :
    fixedWeightSums 1000000000 8750 = (3241457948, 3241459039) := by
  rw [show 8750 = 8500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt8500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt9000 :
    fixedWeightSums 1000000000 9000 = (3244389523, 3244390640) := by
  rw [show 9000 = 8750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt8750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt9250 :
    fixedWeightSums 1000000000 9250 = (3247568840, 3247569986) := by
  rw [show 9250 = 9000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt9000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt9500 :
    fixedWeightSums 1000000000 9500 = (3250872031, 3250873208) := by
  rw [show 9500 = 9250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt9250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

end PrimeFactorUnimodality
