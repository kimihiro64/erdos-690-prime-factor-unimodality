import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums.Part12


/-! Generated fixed-point reciprocal-weight certificates, segment 13. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt29250 :
    fixedWeightSums 1000000000 29250 = (3365827762, 3365830941) := by
  rw [show 29250 = 29000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt29000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt29500 :
    fixedWeightSums 1000000000 29500 = (3366644879, 3366648082) := by
  rw [show 29500 = 29250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt29250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt29750 :
    fixedWeightSums 1000000000 29750 = (3367353953, 3367357177) := by
  rw [show 29750 = 29500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt29500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt30000 :
    fixedWeightSums 1000000000 30000 = (3368057083, 3368060328) := by
  rw [show 30000 = 29750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt29750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt30250 :
    fixedWeightSums 1000000000 30250 = (3368886968, 3368890238) := by
  rw [show 30250 = 30000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt30000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt30500 :
    fixedWeightSums 1000000000 30500 = (3369644250, 3369647543) := by
  rw [show 30500 = 30250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt30250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt30750 :
    fixedWeightSums 1000000000 30750 = (3370362646, 3370365961) := by
  rw [show 30750 = 30500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt30500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt31000 :
    fixedWeightSums 1000000000 31000 = (3371172575, 3371175915) := by
  rw [show 31000 = 30750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt30750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt31250 :
    fixedWeightSums 1000000000 31250 = (3372071821, 3372075189) := by
  rw [show 31250 = 31000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt31000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt31397 :
    fixedWeightSums 1000000000 31397 = (3372582627, 3372586011) := by
  rw [show 31397 = 31250 + 147 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt31250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

end PrimeFactorUnimodality
