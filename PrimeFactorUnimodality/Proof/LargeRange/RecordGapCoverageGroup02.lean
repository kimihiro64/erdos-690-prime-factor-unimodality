import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part13
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part14
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part15
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part16
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part17
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part18
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part19
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part20
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part21
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part22
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part23
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part24

set_option autoImplicit false

/-! Second assembly group for the record-gap composite coverage certificate. -/

namespace PrimeFactorUnimodality

theorem recordGapCoverage_group02 (d : Nat)
    (lower : 84480 ≤ d) (upper : d ≤ 85439)
    (exception_ne : d ≠ 84672) : ¬(recordGapCenter - d).Prime := by
  by_cases h0 : 85360 ≤ d
  · exact recordGapCoverage_part13 d (by omega) (by omega)
  by_cases h1 : 85280 ≤ d
  · exact recordGapCoverage_part14 d (by omega) (by omega)
  by_cases h2 : 85200 ≤ d
  · exact recordGapCoverage_part15 d (by omega) (by omega)
  by_cases h3 : 85120 ≤ d
  · exact recordGapCoverage_part16 d (by omega) (by omega)
  by_cases h4 : 85040 ≤ d
  · exact recordGapCoverage_part17 d (by omega) (by omega)
  by_cases h5 : 84960 ≤ d
  · exact recordGapCoverage_part18 d (by omega) (by omega)
  by_cases h6 : 84880 ≤ d
  · exact recordGapCoverage_part19 d (by omega) (by omega)
  by_cases h7 : 84800 ≤ d
  · exact recordGapCoverage_part20 d (by omega) (by omega)
  by_cases h8 : 84720 ≤ d
  · exact recordGapCoverage_part21 d (by omega) (by omega)
  by_cases h9 : 84640 ≤ d
  · exact recordGapCoverage_part22 d (by omega) (by omega) exception_ne
  by_cases h10 : 84560 ≤ d
  · exact recordGapCoverage_part23 d (by omega) (by omega)
  exact recordGapCoverage_part24 d (by omega) (by omega)

end PrimeFactorUnimodality
