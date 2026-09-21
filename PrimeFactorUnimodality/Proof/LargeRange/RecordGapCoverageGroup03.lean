import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part36
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapCoverageGroup02

set_option autoImplicit false

/-! Generated assembly group 03 for the record-gap coverage certificate. -/

namespace PrimeFactorUnimodality

theorem recordGapCoverage_group03 (d : Nat)
    (lower : 83520 ≤ d) (upper : d ≤ 84479)
    (_exception_ne : d ≠ 84672) : ¬(recordGapCenter - d).Prime := by
  by_cases h0 : 84400 ≤ d
  · exact recordGapCoverage_part25 d (by omega) (by omega)
  by_cases h1 : 84320 ≤ d
  · exact recordGapCoverage_part26 d (by omega) (by omega)
  by_cases h2 : 84240 ≤ d
  · exact recordGapCoverage_part27 d (by omega) (by omega)
  by_cases h3 : 84160 ≤ d
  · exact recordGapCoverage_part28 d (by omega) (by omega)
  by_cases h4 : 84080 ≤ d
  · exact recordGapCoverage_part29 d (by omega) (by omega)
  by_cases h5 : 84000 ≤ d
  · exact recordGapCoverage_part30 d (by omega) (by omega)
  by_cases h6 : 83920 ≤ d
  · exact recordGapCoverage_part31 d (by omega) (by omega)
  by_cases h7 : 83840 ≤ d
  · exact recordGapCoverage_part32 d (by omega) (by omega)
  by_cases h8 : 83760 ≤ d
  · exact recordGapCoverage_part33 d (by omega) (by omega)
  by_cases h9 : 83680 ≤ d
  · exact recordGapCoverage_part34 d (by omega) (by omega)
  by_cases h10 : 83600 ≤ d
  · exact recordGapCoverage_part35 d (by omega) (by omega)
  exact recordGapCoverage_part36 d (by omega) (by omega)

end PrimeFactorUnimodality
