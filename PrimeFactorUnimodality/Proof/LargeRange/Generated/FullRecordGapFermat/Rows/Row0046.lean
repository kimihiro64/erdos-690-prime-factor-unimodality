import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00046_values : List Nat :=
  [fullRecordGapCenterValue - 196804,
    fullRecordGapCenterValue - 196774,
    fullRecordGapCenterValue - 196738,
    fullRecordGapCenterValue - 196608,
    fullRecordGapCenterValue - 196468,
    fullRecordGapCenterValue - 196132,
    fullRecordGapCenterValue - 196114,
    fullRecordGapCenterValue - 196018,
    fullRecordGapCenterValue - 196012,
    fullRecordGapCenterValue - 195964,
    fullRecordGapCenterValue - 195268,
    fullRecordGapCenterValue - 195214,
    fullRecordGapCenterValue - 195124,
    fullRecordGapCenterValue - 195094,
    fullRecordGapCenterValue - 194758,
    fullRecordGapCenterValue - 194644,
    fullRecordGapCenterValue - 194400,
    fullRecordGapCenterValue - 194338,
    fullRecordGapCenterValue - 194254,
    fullRecordGapCenterValue - 194014,
    fullRecordGapCenterValue - 194002,
    fullRecordGapCenterValue - 193654,
    fullRecordGapCenterValue - 193594,
    fullRecordGapCenterValue - 193588,
    fullRecordGapCenterValue - 193162,
    fullRecordGapCenterValue - 192958,
    fullRecordGapCenterValue - 192772,
    fullRecordGapCenterValue - 192034,
    fullRecordGapCenterValue - 192000,
    fullRecordGapCenterValue - 191914,
    fullRecordGapCenterValue - 191908,
    fullRecordGapCenterValue - 191788,
    fullRecordGapCenterValue - 191782,
    fullRecordGapCenterValue - 191664,
    fullRecordGapCenterValue - 191578,
    fullRecordGapCenterValue - 191524,
    fullRecordGapCenterValue - 191242,
    fullRecordGapCenterValue - 191194,
    fullRecordGapCenterValue - 191188,
    fullRecordGapCenterValue - 191098,
    fullRecordGapCenterValue - 191062,
    fullRecordGapCenterValue - 191014,
    fullRecordGapCenterValue - 190972,
    fullRecordGapCenterValue - 190948,
    fullRecordGapCenterValue - 190882,
    fullRecordGapCenterValue - 190858,
    fullRecordGapCenterValue - 190804,
    fullRecordGapCenterValue - 190512,
    fullRecordGapCenterValue - 190462,
    fullRecordGapCenterValue - 190378,
    fullRecordGapCenterValue - 190354,
    fullRecordGapCenterValue - 190080,
    fullRecordGapCenterValue - 190054,
    fullRecordGapCenterValue - 189964,
    fullRecordGapCenterValue - 189922,
    fullRecordGapCenterValue - 189814,
    fullRecordGapCenterValue - 189724,
    fullRecordGapCenterValue - 189454,
    fullRecordGapCenterValue - 189418,
    fullRecordGapCenterValue - 189298,
    fullRecordGapCenterValue - 189268,
    fullRecordGapCenterValue - 189172,
    fullRecordGapCenterValue - 189118,
    fullRecordGapCenterValue - 188878]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00046_fermat : ∀ n ∈ fullRecordGapRow00046_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02881_not_prime : ¬(recordGapCenter - 196804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196804]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02882_not_prime : ¬(recordGapCenter - 196774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196774]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02883_not_prime : ¬(recordGapCenter - 196738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196738]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02884_not_prime : ¬(recordGapCenter - 196608).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196608]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02885_not_prime : ¬(recordGapCenter - 196468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196468]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02886_not_prime : ¬(recordGapCenter - 196132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196132]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02887_not_prime : ¬(recordGapCenter - 196114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196114]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02888_not_prime : ¬(recordGapCenter - 196018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196018]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02889_not_prime : ¬(recordGapCenter - 196012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196012]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02890_not_prime : ¬(recordGapCenter - 195964).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 195964]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02891_not_prime : ¬(recordGapCenter - 195268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 195268]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02892_not_prime : ¬(recordGapCenter - 195214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 195214]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02893_not_prime : ¬(recordGapCenter - 195124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 195124]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02894_not_prime : ¬(recordGapCenter - 195094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 195094]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02895_not_prime : ¬(recordGapCenter - 194758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 194758]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02896_not_prime : ¬(recordGapCenter - 194644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 194644]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02897_not_prime : ¬(recordGapCenter - 194400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 194400]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02898_not_prime : ¬(recordGapCenter - 194338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 194338]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02899_not_prime : ¬(recordGapCenter - 194254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 194254]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02900_not_prime : ¬(recordGapCenter - 194014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 194014]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02901_not_prime : ¬(recordGapCenter - 194002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 194002]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02902_not_prime : ¬(recordGapCenter - 193654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 193654]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02903_not_prime : ¬(recordGapCenter - 193594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 193594]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02904_not_prime : ¬(recordGapCenter - 193588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 193588]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02905_not_prime : ¬(recordGapCenter - 193162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 193162]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02906_not_prime : ¬(recordGapCenter - 192958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 192958]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02907_not_prime : ¬(recordGapCenter - 192772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 192772]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02908_not_prime : ¬(recordGapCenter - 192034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 192034]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02909_not_prime : ¬(recordGapCenter - 192000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 192000]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02910_not_prime : ¬(recordGapCenter - 191914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191914]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02911_not_prime : ¬(recordGapCenter - 191908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191908]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02912_not_prime : ¬(recordGapCenter - 191788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191788]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02913_not_prime : ¬(recordGapCenter - 191782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191782]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02914_not_prime : ¬(recordGapCenter - 191664).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191664]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02915_not_prime : ¬(recordGapCenter - 191578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191578]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02916_not_prime : ¬(recordGapCenter - 191524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191524]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02917_not_prime : ¬(recordGapCenter - 191242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191242]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02918_not_prime : ¬(recordGapCenter - 191194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191194]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02919_not_prime : ¬(recordGapCenter - 191188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191188]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02920_not_prime : ¬(recordGapCenter - 191098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191098]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02921_not_prime : ¬(recordGapCenter - 191062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191062]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02922_not_prime : ¬(recordGapCenter - 191014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191014]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02923_not_prime : ¬(recordGapCenter - 190972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190972]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02924_not_prime : ¬(recordGapCenter - 190948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190948]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02925_not_prime : ¬(recordGapCenter - 190882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190882]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02926_not_prime : ¬(recordGapCenter - 190858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190858]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02927_not_prime : ¬(recordGapCenter - 190804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190804]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02928_not_prime : ¬(recordGapCenter - 190512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190512]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02929_not_prime : ¬(recordGapCenter - 190462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190462]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02930_not_prime : ¬(recordGapCenter - 190378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190378]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02931_not_prime : ¬(recordGapCenter - 190354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190354]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02932_not_prime : ¬(recordGapCenter - 190080).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190080]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02933_not_prime : ¬(recordGapCenter - 190054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190054]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02934_not_prime : ¬(recordGapCenter - 189964).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189964]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02935_not_prime : ¬(recordGapCenter - 189922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189922]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02936_not_prime : ¬(recordGapCenter - 189814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189814]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02937_not_prime : ¬(recordGapCenter - 189724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189724]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02938_not_prime : ¬(recordGapCenter - 189454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189454]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02939_not_prime : ¬(recordGapCenter - 189418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189418]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02940_not_prime : ¬(recordGapCenter - 189298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189298]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02941_not_prime : ¬(recordGapCenter - 189268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189268]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02942_not_prime : ¬(recordGapCenter - 189172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189172]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02943_not_prime : ¬(recordGapCenter - 189118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189118]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

theorem fullRecordGapTerm02944_not_prime : ¬(recordGapCenter - 188878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188878]
  · apply fullRecordGapRow00046_fermat
    simp [fullRecordGapRow00046_values]

end PrimeFactorUnimodality
