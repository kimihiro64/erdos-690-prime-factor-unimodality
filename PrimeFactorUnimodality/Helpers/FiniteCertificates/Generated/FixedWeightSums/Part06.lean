import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums.Part05


/-! Generated fixed-point reciprocal-weight certificates, segment 6. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt12250 :
    fixedWeightSums 1000000000 12250 = (3277332811, 3277334274) := by
  rw [show 12250 = 12000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt12000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt12500 :
    fixedWeightSums 1000000000 12500 = (3279676385, 3279677877) := by
  rw [show 12500 = 12250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt12250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt12750 :
    fixedWeightSums 1000000000 12750 = (3281974984, 3281976505) := by
  rw [show 12750 = 12500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt12500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt13000 :
    fixedWeightSums 1000000000 13000 = (3283993823, 3283995370) := by
  rw [show 13000 = 12750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt12750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt13250 :
    fixedWeightSums 1000000000 13250 = (3286128019, 3286129594) := by
  rw [show 13250 = 13000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt13000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt13500 :
    fixedWeightSums 1000000000 13500 = (3287996064, 3287997664) := by
  rw [show 13500 = 13250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt13250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt13750 :
    fixedWeightSums 1000000000 13750 = (3289829135, 3289830760) := by
  rw [show 13750 = 13500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt13500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt14000 :
    fixedWeightSums 1000000000 14000 = (3291776363, 3291778015) := by
  rw [show 14000 = 13750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt13750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt14250 :
    fixedWeightSums 1000000000 14250 = (3293334326, 3293336000) := by
  rw [show 14250 = 14000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt14000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt14500 :
    fixedWeightSums 1000000000 14500 = (3295003133, 3295004831) := by
  rw [show 14500 = 14250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt14250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

end PrimeFactorUnimodality
