import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part48
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapCoverageGroup03

set_option autoImplicit false

/-! Generated assembly group 04 for the record-gap coverage certificate. -/

namespace PrimeFactorUnimodality

theorem recordGapCoverage_group04 (d : Nat)
    (lower : 82560 ≤ d) (upper : d ≤ 83519)
    (_exception_ne : d ≠ 84672) : ¬(recordGapCenter - d).Prime := by
  by_cases h0 : 83440 ≤ d
  · exact recordGapCoverage_part37 d (by omega) (by omega)
  by_cases h1 : 83360 ≤ d
  · exact recordGapCoverage_part38 d (by omega) (by omega)
  by_cases h2 : 83280 ≤ d
  · exact recordGapCoverage_part39 d (by omega) (by omega)
  by_cases h3 : 83200 ≤ d
  · exact recordGapCoverage_part40 d (by omega) (by omega)
  by_cases h4 : 83120 ≤ d
  · exact recordGapCoverage_part41 d (by omega) (by omega)
  by_cases h5 : 83040 ≤ d
  · exact recordGapCoverage_part42 d (by omega) (by omega)
  by_cases h6 : 82960 ≤ d
  · exact recordGapCoverage_part43 d (by omega) (by omega)
  by_cases h7 : 82880 ≤ d
  · exact recordGapCoverage_part44 d (by omega) (by omega)
  by_cases h8 : 82800 ≤ d
  · exact recordGapCoverage_part45 d (by omega) (by omega)
  by_cases h9 : 82720 ≤ d
  · exact recordGapCoverage_part46 d (by omega) (by omega)
  by_cases h10 : 82640 ≤ d
  · exact recordGapCoverage_part47 d (by omega) (by omega)
  exact recordGapCoverage_part48 d (by omega) (by omega)

end PrimeFactorUnimodality
