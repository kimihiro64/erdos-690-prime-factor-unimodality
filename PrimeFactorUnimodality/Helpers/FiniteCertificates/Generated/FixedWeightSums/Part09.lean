import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums.Part08


/-! Generated fixed-point reciprocal-weight certificates, segment 9. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt19250 :
    fixedWeightSums 1000000000 19250 = (3324059598, 3324061781) := by
  rw [show 19250 = 19000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt19000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt19500 :
    fixedWeightSums 1000000000 19500 = (3325555029, 3325557241) := by
  rw [show 19500 = 19250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt19250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt19750 :
    fixedWeightSums 1000000000 19750 = (3326676521, 3326678755) := by
  rw [show 19750 = 19500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt19500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt20000 :
    fixedWeightSums 1000000000 20000 = (3328085217, 3328087479) := by
  rw [show 20000 = 19750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt19750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt20250 :
    fixedWeightSums 1000000000 20250 = (3329426936, 3329429225) := by
  rw [show 20250 = 20000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt20000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt20500 :
    fixedWeightSums 1000000000 20500 = (3330604964, 3330607277) := by
  rw [show 20500 = 20250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt20250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt20750 :
    fixedWeightSums 1000000000 20750 = (3331768344, 3331770681) := by
  rw [show 20750 = 20500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt20500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt21000 :
    fixedWeightSums 1000000000 21000 = (3332870192, 3332872552) := by
  rw [show 21000 = 20750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt20750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt21250 :
    fixedWeightSums 1000000000 21250 = (3334196159, 3334198547) := by
  rw [show 21250 = 21000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt21000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt21500 :
    fixedWeightSums 1000000000 21500 = (3335318374, 3335320786) := by
  rw [show 21500 = 21250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt21250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

end PrimeFactorUnimodality
