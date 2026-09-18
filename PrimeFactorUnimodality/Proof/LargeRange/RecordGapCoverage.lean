import PrimeFactorUnimodality.Proof.LargeRange.RecordGapCoverageGroup01
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapCoverageGroup02
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapCoverageGroup03
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapCoverageGroup04
import PrimeFactorUnimodality.Proof.LargeRange.RecordGapCoverageGroup05

set_option autoImplicit false

/-! Assembly of the generated composite coverage for the record-gap block. -/

namespace PrimeFactorUnimodality

theorem recordGapCoverage (d : Nat) (lower : 81649 ≤ d) (upper : d ≤ 86399)
    (exception_ne : d ≠ 84672) : ¬(recordGapCenter - d).Prime := by
  by_cases h1 : 85440 ≤ d
  · exact recordGapCoverage_group01 d (by omega) (by omega) exception_ne
  by_cases h2 : 84480 ≤ d
  · exact recordGapCoverage_group02 d (by omega) (by omega) exception_ne
  by_cases h3 : 83520 ≤ d
  · exact recordGapCoverage_group03 d (by omega) (by omega) exception_ne
  by_cases h4 : 82560 ≤ d
  · exact recordGapCoverage_group04 d (by omega) (by omega) exception_ne
  exact recordGapCoverage_group05 d (by omega) (by omega) exception_ne

end PrimeFactorUnimodality
