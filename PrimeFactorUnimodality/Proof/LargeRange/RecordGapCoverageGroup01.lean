import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part12

set_option autoImplicit false

/-! Generated assembly group 01 for the record-gap coverage certificate. -/

namespace PrimeFactorUnimodality

theorem recordGapCoverage_group01 (d : Nat)
    (lower : 85440 ≤ d) (upper : d ≤ 86399)
    (_exception_ne : d ≠ 84672) : ¬(recordGapCenter - d).Prime := by
  by_cases h0 : 86320 ≤ d
  · exact recordGapCoverage_part01 d (by omega) (by omega)
  by_cases h1 : 86240 ≤ d
  · exact recordGapCoverage_part02 d (by omega) (by omega)
  by_cases h2 : 86160 ≤ d
  · exact recordGapCoverage_part03 d (by omega) (by omega)
  by_cases h3 : 86080 ≤ d
  · exact recordGapCoverage_part04 d (by omega) (by omega)
  by_cases h4 : 86000 ≤ d
  · exact recordGapCoverage_part05 d (by omega) (by omega)
  by_cases h5 : 85920 ≤ d
  · exact recordGapCoverage_part06 d (by omega) (by omega)
  by_cases h6 : 85840 ≤ d
  · exact recordGapCoverage_part07 d (by omega) (by omega)
  by_cases h7 : 85760 ≤ d
  · exact recordGapCoverage_part08 d (by omega) (by omega)
  by_cases h8 : 85680 ≤ d
  · exact recordGapCoverage_part09 d (by omega) (by omega)
  by_cases h9 : 85600 ≤ d
  · exact recordGapCoverage_part10 d (by omega) (by omega)
  by_cases h10 : 85520 ≤ d
  · exact recordGapCoverage_part11 d (by omega) (by omega)
  exact recordGapCoverage_part12 d (by omega) (by omega)

end PrimeFactorUnimodality
