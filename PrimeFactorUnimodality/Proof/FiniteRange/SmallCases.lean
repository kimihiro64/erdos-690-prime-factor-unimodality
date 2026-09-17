import PrimeFactorUnimodality.Proof.FiniteRange.Generated.K04To12
import PrimeFactorUnimodality.Proof.FiniteRange.Generated.K13To20

/-! Exact finite certificates for k = 4,...,20. -/

namespace PrimeFactorUnimodality

theorem smallRangePrimeFactorDensity_not_isUnimodal
    (k : Nat) (hLower : 4 ≤ k) (hUpper : k ≤ 20) :
    ¬ IsUnimodal (primeFactorDensity k) := by
  interval_cases k
  all_goals first
    | exact k4PrimeFactorDensity_not_isUnimodal
    | exact k5PrimeFactorDensity_not_isUnimodal
    | exact k6PrimeFactorDensity_not_isUnimodal
    | exact k7PrimeFactorDensity_not_isUnimodal
    | exact k8PrimeFactorDensity_not_isUnimodal
    | exact k9PrimeFactorDensity_not_isUnimodal
    | exact k10PrimeFactorDensity_not_isUnimodal
    | exact k11PrimeFactorDensity_not_isUnimodal
    | exact k12PrimeFactorDensity_not_isUnimodal
    | exact k13PrimeFactorDensity_not_isUnimodal
    | exact k14PrimeFactorDensity_not_isUnimodal
    | exact k15PrimeFactorDensity_not_isUnimodal
    | exact k16PrimeFactorDensity_not_isUnimodal
    | exact k17PrimeFactorDensity_not_isUnimodal
    | exact k18PrimeFactorDensity_not_isUnimodal
    | exact k19PrimeFactorDensity_not_isUnimodal
    | exact k20PrimeFactorDensity_not_isUnimodal

end PrimeFactorUnimodality
