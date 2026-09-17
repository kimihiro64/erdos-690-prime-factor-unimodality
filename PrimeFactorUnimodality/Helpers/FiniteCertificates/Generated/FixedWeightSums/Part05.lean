import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums.Part04


/-! Generated fixed-point reciprocal-weight certificates, segment 5. -/

set_option autoImplicit false

namespace PrimeFactorUnimodality

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt9750 :
    fixedWeightSums 1000000000 9750 = (3253569934, 3253571137) := by
  rw [show 9750 = 9500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt9500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt10000 :
    fixedWeightSums 1000000000 10000 = (3256206224, 3256207453) := by
  rw [show 10000 = 9750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt9750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt10250 :
    fixedWeightSums 1000000000 10250 = (3258873065, 3258874321) := by
  rw [show 10250 = 10000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt10000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt10500 :
    fixedWeightSums 1000000000 10500 = (3261574172, 3261575456) := by
  rw [show 10500 = 10250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt10250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt10750 :
    fixedWeightSums 1000000000 10750 = (3264019661, 3264020971) := by
  rw [show 10750 = 10500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt10500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt11000 :
    fixedWeightSums 1000000000 11000 = (3266317435, 3266318770) := by
  rw [show 11000 = 10750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt10750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt11250 :
    fixedWeightSums 1000000000 11250 = (3268475333, 3268476692) := by
  rw [show 11250 = 11000 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt11000]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt11500 :
    fixedWeightSums 1000000000 11500 = (3270937257, 3270938644) := by
  rw [show 11500 = 11250 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt11250]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt11750 :
    fixedWeightSums 1000000000 11750 = (3272828921, 3272830330) := by
  rw [show 11750 = 11500 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt11500]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
-- Transparent trial division for this bounded block needs a deterministic enlarged budget.
theorem fixedWeightSumsAt12000 :
    fixedWeightSums 1000000000 12000 = (3275270349, 3275271787) := by
  rw [show 12000 = 11750 + 250 by norm_num,
    fixedWeightSums_add, fixedWeightSumsAt11750]
  norm_num [iterateFixedWeightSteps, fixedWeightStep, isPrimeTrial, Nat.minFac,
    Nat.minFacAux]

end PrimeFactorUnimodality
