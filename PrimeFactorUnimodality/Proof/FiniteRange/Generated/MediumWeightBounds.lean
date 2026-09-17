import PrimeFactorUnimodality.Helpers.FiniteCertificates.Generated.FixedWeightSums

set_option autoImplicit false

/-! Generated rational reciprocal-weight bounds for the medium finite range. -/

namespace PrimeFactorUnimodality

theorem weightSumPrimesBelow113Upper :
    weightSum (primesBelow 113) ≤ (2612642184 : Rat) / 1000000000 := by
  exact fixedWeightSums_upper_bound 1000000000 113 2612642155 2612642184
    (by norm_num) fixedWeightSumsAt113

theorem weightSumPrimesBelow211Upper :
    weightSum (primesBelow 211) ≤ (2721441036 : Rat) / 1000000000 := by
  exact fixedWeightSums_upper_bound 1000000000 211 2721440990 2721441036
    (by norm_num) fixedWeightSumsAt211

theorem weightSumPrimesBelow15683Lower :
    (3303754306 : Rat) / 1000000000 ≤ weightSum (primesBelow 15683) := by
  exact fixedWeightSums_lower_bound 1000000000 15683 3303754306 3303756136
    (by norm_num) fixedWeightSumsAt15683

theorem weightSumPrimesBelow15727Lower :
    (3303818073 : Rat) / 1000000000 ≤ weightSum (primesBelow 15727) := by
  exact fixedWeightSums_lower_bound 1000000000 15727 3303818073 3303819904
    (by norm_num) fixedWeightSumsAt15727

theorem weightSumPrimesBelow15727Upper :
    weightSum (primesBelow 15727) ≤ (3303819904 : Rat) / 1000000000 := by
  exact fixedWeightSums_upper_bound 1000000000 15727 3303818073 3303819904
    (by norm_num) fixedWeightSumsAt15727

theorem weightSumPrimesBelow31397Lower :
    (3372582627 : Rat) / 1000000000 ≤ weightSum (primesBelow 31397) := by
  exact fixedWeightSums_lower_bound 1000000000 31397 3372582627 3372586011
    (by norm_num) fixedWeightSumsAt31397

theorem weightSumPrimesBelow31469Lower :
    (3372614478 : Rat) / 1000000000 ≤ weightSum (primesBelow 31469) := by
  exact fixedWeightSums_lower_bound 1000000000 31469 3372614478 3372617863
    (by norm_num) fixedWeightSumsAt31469

theorem weightSumPrimesBelow31469Upper :
    weightSum (primesBelow 31469) ≤ (3372617863 : Rat) / 1000000000 := by
  exact fixedWeightSums_upper_bound 1000000000 31469 3372614478 3372617863
    (by norm_num) fixedWeightSumsAt31469

end PrimeFactorUnimodality
