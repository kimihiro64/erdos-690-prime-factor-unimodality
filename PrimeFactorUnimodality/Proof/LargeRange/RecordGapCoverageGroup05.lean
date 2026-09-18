import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part49
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part50
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part51
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part52
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part53
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part54
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part55
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part56
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part57
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part58
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part59
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part60

set_option autoImplicit false

/-! Fifth assembly group for the record-gap composite coverage certificate. -/

namespace PrimeFactorUnimodality

theorem recordGapCoverage_group05 (d : Nat)
    (lower : 81649 ≤ d) (upper : d ≤ 82559)
    (_exception_ne : d ≠ 84672) : ¬(recordGapCenter - d).Prime := by
  by_cases h0 : 82480 ≤ d
  · exact recordGapCoverage_part49 d (by omega) (by omega)
  by_cases h1 : 82400 ≤ d
  · exact recordGapCoverage_part50 d (by omega) (by omega)
  by_cases h2 : 82320 ≤ d
  · exact recordGapCoverage_part51 d (by omega) (by omega)
  by_cases h3 : 82240 ≤ d
  · exact recordGapCoverage_part52 d (by omega) (by omega)
  by_cases h4 : 82160 ≤ d
  · exact recordGapCoverage_part53 d (by omega) (by omega)
  by_cases h5 : 82080 ≤ d
  · exact recordGapCoverage_part54 d (by omega) (by omega)
  by_cases h6 : 82000 ≤ d
  · exact recordGapCoverage_part55 d (by omega) (by omega)
  by_cases h7 : 81920 ≤ d
  · exact recordGapCoverage_part56 d (by omega) (by omega)
  by_cases h8 : 81840 ≤ d
  · exact recordGapCoverage_part57 d (by omega) (by omega)
  by_cases h9 : 81760 ≤ d
  · exact recordGapCoverage_part58 d (by omega) (by omega)
  by_cases h10 : 81680 ≤ d
  · exact recordGapCoverage_part59 d (by omega) (by omega)
  exact recordGapCoverage_part60 d (by omega) (by omega)

end PrimeFactorUnimodality
