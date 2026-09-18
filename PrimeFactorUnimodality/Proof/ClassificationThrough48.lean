import PrimeFactorUnimodality.Proof.FiniteRange.MediumCases
import PrimeFactorUnimodality.Proof.FiniteRange.SmallCases
import PrimeFactorUnimodality.Proof.Unimodality.PositiveCases

set_option autoImplicit false

namespace PrimeFactorUnimodality

/-! Finite classification covered by the generated certificates. -/
theorem completeClassification_through48
    (k : Nat) (hk : 1 ≤ k) (hk48 : k ≤ 48) :
    IsUnimodal (primeFactorDensity k) ↔ k ≤ 3 := by
  constructor
  · intro hu
    by_contra hnot
    have hk4 : 4 ≤ k := by omega
    by_cases hsmall : k ≤ 20
    · exact (smallRangePrimeFactorDensity_not_isUnimodal k hk4 hsmall) hu
    · exact (mediumRangePrimeFactorDensity_not_isUnimodal k (by omega) hk48) hu
  · intro hk3
    have hcases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact firstPrimeFactorDensity_isUnimodal
    · exact secondPrimeFactorDensity_isUnimodal
    · exact thirdPrimeFactorDensity_isUnimodal

end PrimeFactorUnimodality
