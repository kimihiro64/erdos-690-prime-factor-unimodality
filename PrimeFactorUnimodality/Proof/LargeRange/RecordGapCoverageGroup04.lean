import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part37
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part38
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part39
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part40
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part41
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part42
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part43
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part44
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part45
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part46
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part47
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapCoverage.Part48

set_option autoImplicit false

/-! Fourth assembly group for the record-gap composite coverage certificate. -/

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
