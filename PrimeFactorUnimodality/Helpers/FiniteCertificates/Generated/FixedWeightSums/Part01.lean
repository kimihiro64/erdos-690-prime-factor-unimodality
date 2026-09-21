import Mathlib.Tactic.NormNum
import PrimeFactorUnimodality.Helpers.FiniteCertificates.CertifiedWeightSum
import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.PrimePrefixes


/-! Generated fixed-point reciprocal-weight certificates, segment 1. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

theorem fixedWeightSumsAt0 :
    fixedWeightSums 1000000000 0 = (0, 0) := by
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt113 :
    fixedWeightSums 1000000000 113 = (2612642155, 2612642184) := by
  rw [show 113 = 0 + 113 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt0]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt211 :
    fixedWeightSums 1000000000 211 = (2721440990, 2721441036) := by
  rw [show 211 = 113 + 98 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt113]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt250 :
    fixedWeightSums 1000000000 250 = (2752196830, 2752196883) := by
  rw [show 250 = 211 + 39 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt211]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt500 :
    fixedWeightSums 1000000000 500 = (2869592665, 2869592760) := by
  rw [show 500 = 250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt750 :
    fixedWeightSums 1000000000 750 = (2929551553, 2929551685) := by
  rw [show 750 = 500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt1000 :
    fixedWeightSums 1000000000 1000 = (2971109659, 2971109827) := by
  rw [show 1000 = 750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt1250 :
    fixedWeightSums 1000000000 1250 = (3003353219, 3003353423) := by
  rw [show 1250 = 1000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt1000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt1500 :
    fixedWeightSums 1000000000 1500 = (3028705140, 3028705379) := by
  rw [show 1500 = 1250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt1250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt1750 :
    fixedWeightSums 1000000000 1750 = (3049025363, 3049025635) := by
  rw [show 1750 = 1500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt1500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt2000 :
    fixedWeightSums 1000000000 2000 = (3065546693, 3065546996) := by
  rw [show 2000 = 1750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt1750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

end PrimeFactorUnimodality
