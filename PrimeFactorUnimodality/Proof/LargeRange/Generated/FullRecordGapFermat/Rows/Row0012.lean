import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00012_values : List Nat :=
  [fullRecordGapCenterValue - 205222,
    fullRecordGapCenterValue - 205174,
    fullRecordGapCenterValue - 204994,
    fullRecordGapCenterValue - 204658,
    fullRecordGapCenterValue - 204634,
    fullRecordGapCenterValue - 204298,
    fullRecordGapCenterValue - 204214,
    fullRecordGapCenterValue - 204154,
    fullRecordGapCenterValue - 203758,
    fullRecordGapCenterValue - 203742,
    fullRecordGapCenterValue - 203254,
    fullRecordGapCenterValue - 203074,
    fullRecordGapCenterValue - 203068,
    fullRecordGapCenterValue - 203062,
    fullRecordGapCenterValue - 202858,
    fullRecordGapCenterValue - 202828,
    fullRecordGapCenterValue - 202534,
    fullRecordGapCenterValue - 202348,
    fullRecordGapCenterValue - 202324,
    fullRecordGapCenterValue - 202222,
    fullRecordGapCenterValue - 202012,
    fullRecordGapCenterValue - 201988,
    fullRecordGapCenterValue - 201862,
    fullRecordGapCenterValue - 201814,
    fullRecordGapCenterValue - 201694,
    fullRecordGapCenterValue - 201532,
    fullRecordGapCenterValue - 201364,
    fullRecordGapCenterValue - 201298,
    fullRecordGapCenterValue - 200542,
    fullRecordGapCenterValue - 200338,
    fullRecordGapCenterValue - 200218,
    fullRecordGapCenterValue - 200212,
    fullRecordGapCenterValue - 199978,
    fullRecordGapCenterValue - 199650,
    fullRecordGapCenterValue - 199414,
    fullRecordGapCenterValue - 199204,
    fullRecordGapCenterValue - 198988,
    fullRecordGapCenterValue - 198844,
    fullRecordGapCenterValue - 198742,
    fullRecordGapCenterValue - 198634,
    fullRecordGapCenterValue - 198508,
    fullRecordGapCenterValue - 198382,
    fullRecordGapCenterValue - 198274,
    fullRecordGapCenterValue - 198238,
    fullRecordGapCenterValue - 198148,
    fullRecordGapCenterValue - 198082,
    fullRecordGapCenterValue - 198034,
    fullRecordGapCenterValue - 197908,
    fullRecordGapCenterValue - 197878,
    fullRecordGapCenterValue - 197854,
    fullRecordGapCenterValue - 197818,
    fullRecordGapCenterValue - 197734,
    fullRecordGapCenterValue - 197668,
    fullRecordGapCenterValue - 197644,
    fullRecordGapCenterValue - 197614,
    fullRecordGapCenterValue - 197602,
    fullRecordGapCenterValue - 197452,
    fullRecordGapCenterValue - 197332,
    fullRecordGapCenterValue - 197194,
    fullRecordGapCenterValue - 197188,
    fullRecordGapCenterValue - 197122,
    fullRecordGapCenterValue - 196858,
    fullRecordGapCenterValue - 196830,
    fullRecordGapCenterValue - 196828,
    fullRecordGapCenterValue - 196804,
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
    fullRecordGapCenterValue - 188878,
    fullRecordGapCenterValue - 188794,
    fullRecordGapCenterValue - 188662,
    fullRecordGapCenterValue - 188548,
    fullRecordGapCenterValue - 188458,
    fullRecordGapCenterValue - 188218,
    fullRecordGapCenterValue - 188164,
    fullRecordGapCenterValue - 188160,
    fullRecordGapCenterValue - 188158,
    fullRecordGapCenterValue - 187822,
    fullRecordGapCenterValue - 187732,
    fullRecordGapCenterValue - 187522,
    fullRecordGapCenterValue - 187500,
    fullRecordGapCenterValue - 187438,
    fullRecordGapCenterValue - 187324,
    fullRecordGapCenterValue - 187084,
    fullRecordGapCenterValue - 186994,
    fullRecordGapCenterValue - 186988,
    fullRecordGapCenterValue - 186958,
    fullRecordGapCenterValue - 186724,
    fullRecordGapCenterValue - 186624,
    fullRecordGapCenterValue - 186574,
    fullRecordGapCenterValue - 186478,
    fullRecordGapCenterValue - 186340,
    fullRecordGapCenterValue - 186268,
    fullRecordGapCenterValue - 186262,
    fullRecordGapCenterValue - 186178,
    fullRecordGapCenterValue - 186094,
    fullRecordGapCenterValue - 186028,
    fullRecordGapCenterValue - 185908,
    fullRecordGapCenterValue - 185884,
    fullRecordGapCenterValue - 185842,
    fullRecordGapCenterValue - 185698,
    fullRecordGapCenterValue - 185404,
    fullRecordGapCenterValue - 185220,
    fullRecordGapCenterValue - 185092,
    fullRecordGapCenterValue - 185044,
    fullRecordGapCenterValue - 184800,
    fullRecordGapCenterValue - 184774,
    fullRecordGapCenterValue - 184762,
    fullRecordGapCenterValue - 184714,
    fullRecordGapCenterValue - 184588,
    fullRecordGapCenterValue - 184378,
    fullRecordGapCenterValue - 184354,
    fullRecordGapCenterValue - 184018,
    fullRecordGapCenterValue - 183994,
    fullRecordGapCenterValue - 183934,
    fullRecordGapCenterValue - 183750,
    fullRecordGapCenterValue - 183622,
    fullRecordGapCenterValue - 183412,
    fullRecordGapCenterValue - 183382,
    fullRecordGapCenterValue - 183262,
    fullRecordGapCenterValue - 183028,
    fullRecordGapCenterValue - 183004,
    fullRecordGapCenterValue - 182952,
    fullRecordGapCenterValue - 182914,
    fullRecordGapCenterValue - 182794,
    fullRecordGapCenterValue - 182788,
    fullRecordGapCenterValue - 182662,
    fullRecordGapCenterValue - 182524,
    fullRecordGapCenterValue - 182458,
    fullRecordGapCenterValue - 182254,
    fullRecordGapCenterValue - 182250,
    fullRecordGapCenterValue - 182194,
    fullRecordGapCenterValue - 181942,
    fullRecordGapCenterValue - 181894,
    fullRecordGapCenterValue - 181822,
    fullRecordGapCenterValue - 181642,
    fullRecordGapCenterValue - 181444,
    fullRecordGapCenterValue - 181348,
    fullRecordGapCenterValue - 181318,
    fullRecordGapCenterValue - 181234,
    fullRecordGapCenterValue - 180988,
    fullRecordGapCenterValue - 180802,
    fullRecordGapCenterValue - 180724,
    fullRecordGapCenterValue - 180394,
    fullRecordGapCenterValue - 180178,
    fullRecordGapCenterValue - 180142,
    fullRecordGapCenterValue - 180022,
    fullRecordGapCenterValue - 179878,
    fullRecordGapCenterValue - 179818,
    fullRecordGapCenterValue - 179794,
    fullRecordGapCenterValue - 179734,
    fullRecordGapCenterValue - 179668,
    fullRecordGapCenterValue - 179638,
    fullRecordGapCenterValue - 179548,
    fullRecordGapCenterValue - 179200,
    fullRecordGapCenterValue - 179188,
    fullRecordGapCenterValue - 179092,
    fullRecordGapCenterValue - 179038,
    fullRecordGapCenterValue - 178954,
    fullRecordGapCenterValue - 178762,
    fullRecordGapCenterValue - 178588,
    fullRecordGapCenterValue - 178378,
    fullRecordGapCenterValue - 178252,
    fullRecordGapCenterValue - 178114,
    fullRecordGapCenterValue - 178042,
    fullRecordGapCenterValue - 177870,
    fullRecordGapCenterValue - 177634,
    fullRecordGapCenterValue - 177622,
    fullRecordGapCenterValue - 177532,
    fullRecordGapCenterValue - 177408,
    fullRecordGapCenterValue - 176854,
    fullRecordGapCenterValue - 176794,
    fullRecordGapCenterValue - 176418,
    fullRecordGapCenterValue - 176284,
    fullRecordGapCenterValue - 176074,
    fullRecordGapCenterValue - 175948,
    fullRecordGapCenterValue - 175822,
    fullRecordGapCenterValue - 175774,
    fullRecordGapCenterValue - 175738,
    fullRecordGapCenterValue - 175402,
    fullRecordGapCenterValue - 175114,
    fullRecordGapCenterValue - 175018,
    fullRecordGapCenterValue - 175000,
    fullRecordGapCenterValue - 174982,
    fullRecordGapCenterValue - 174604,
    fullRecordGapCenterValue - 174562,
    fullRecordGapCenterValue - 174514,
    fullRecordGapCenterValue - 174502,
    fullRecordGapCenterValue - 174358,
    fullRecordGapCenterValue - 174292,
    fullRecordGapCenterValue - 173962,
    fullRecordGapCenterValue - 173938,
    fullRecordGapCenterValue - 173854,
    fullRecordGapCenterValue - 173764,
    fullRecordGapCenterValue - 173722,
    fullRecordGapCenterValue - 173674,
    fullRecordGapCenterValue - 173284]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00012_fermat : ∀ n ∈ fullRecordGapRow00012_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02817_not_prime : ¬(recordGapCenter - 205222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 205222]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02818_not_prime : ¬(recordGapCenter - 205174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 205174]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02819_not_prime : ¬(recordGapCenter - 204994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 204994]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02820_not_prime : ¬(recordGapCenter - 204658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 204658]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02821_not_prime : ¬(recordGapCenter - 204634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 204634]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02822_not_prime : ¬(recordGapCenter - 204298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 204298]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02823_not_prime : ¬(recordGapCenter - 204214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 204214]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02824_not_prime : ¬(recordGapCenter - 204154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 204154]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02825_not_prime : ¬(recordGapCenter - 203758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 203758]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02826_not_prime : ¬(recordGapCenter - 203742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 203742]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02827_not_prime : ¬(recordGapCenter - 203254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 203254]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02828_not_prime : ¬(recordGapCenter - 203074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 203074]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02829_not_prime : ¬(recordGapCenter - 203068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 203068]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02830_not_prime : ¬(recordGapCenter - 203062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 203062]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02831_not_prime : ¬(recordGapCenter - 202858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 202858]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02832_not_prime : ¬(recordGapCenter - 202828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 202828]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02833_not_prime : ¬(recordGapCenter - 202534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 202534]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02834_not_prime : ¬(recordGapCenter - 202348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 202348]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02835_not_prime : ¬(recordGapCenter - 202324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 202324]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02836_not_prime : ¬(recordGapCenter - 202222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 202222]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02837_not_prime : ¬(recordGapCenter - 202012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 202012]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02838_not_prime : ¬(recordGapCenter - 201988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 201988]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02839_not_prime : ¬(recordGapCenter - 201862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 201862]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02840_not_prime : ¬(recordGapCenter - 201814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 201814]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02841_not_prime : ¬(recordGapCenter - 201694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 201694]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02842_not_prime : ¬(recordGapCenter - 201532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 201532]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02843_not_prime : ¬(recordGapCenter - 201364).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 201364]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02844_not_prime : ¬(recordGapCenter - 201298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 201298]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02845_not_prime : ¬(recordGapCenter - 200542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 200542]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02846_not_prime : ¬(recordGapCenter - 200338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 200338]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02847_not_prime : ¬(recordGapCenter - 200218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 200218]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02848_not_prime : ¬(recordGapCenter - 200212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 200212]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02849_not_prime : ¬(recordGapCenter - 199978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 199978]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02850_not_prime : ¬(recordGapCenter - 199650).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 199650]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02851_not_prime : ¬(recordGapCenter - 199414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 199414]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02852_not_prime : ¬(recordGapCenter - 199204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 199204]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02853_not_prime : ¬(recordGapCenter - 198988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198988]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02854_not_prime : ¬(recordGapCenter - 198844).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198844]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02855_not_prime : ¬(recordGapCenter - 198742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198742]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02856_not_prime : ¬(recordGapCenter - 198634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198634]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02857_not_prime : ¬(recordGapCenter - 198508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198508]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02858_not_prime : ¬(recordGapCenter - 198382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198382]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02859_not_prime : ¬(recordGapCenter - 198274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198274]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02860_not_prime : ¬(recordGapCenter - 198238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198238]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02861_not_prime : ¬(recordGapCenter - 198148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198148]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02862_not_prime : ¬(recordGapCenter - 198082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198082]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02863_not_prime : ¬(recordGapCenter - 198034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 198034]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02864_not_prime : ¬(recordGapCenter - 197908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197908]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02865_not_prime : ¬(recordGapCenter - 197878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197878]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02866_not_prime : ¬(recordGapCenter - 197854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197854]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02867_not_prime : ¬(recordGapCenter - 197818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197818]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02868_not_prime : ¬(recordGapCenter - 197734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197734]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02869_not_prime : ¬(recordGapCenter - 197668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197668]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02870_not_prime : ¬(recordGapCenter - 197644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197644]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02871_not_prime : ¬(recordGapCenter - 197614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197614]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02872_not_prime : ¬(recordGapCenter - 197602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197602]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02873_not_prime : ¬(recordGapCenter - 197452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197452]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02874_not_prime : ¬(recordGapCenter - 197332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197332]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02875_not_prime : ¬(recordGapCenter - 197194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197194]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02876_not_prime : ¬(recordGapCenter - 197188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197188]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02877_not_prime : ¬(recordGapCenter - 197122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 197122]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02878_not_prime : ¬(recordGapCenter - 196858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196858]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02879_not_prime : ¬(recordGapCenter - 196830).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196830]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02880_not_prime : ¬(recordGapCenter - 196828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196828]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02881_not_prime : ¬(recordGapCenter - 196804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196804]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02882_not_prime : ¬(recordGapCenter - 196774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196774]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02883_not_prime : ¬(recordGapCenter - 196738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196738]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02884_not_prime : ¬(recordGapCenter - 196608).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196608]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02885_not_prime : ¬(recordGapCenter - 196468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196468]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02886_not_prime : ¬(recordGapCenter - 196132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196132]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02887_not_prime : ¬(recordGapCenter - 196114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196114]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02888_not_prime : ¬(recordGapCenter - 196018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196018]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02889_not_prime : ¬(recordGapCenter - 196012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 196012]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02890_not_prime : ¬(recordGapCenter - 195964).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 195964]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02891_not_prime : ¬(recordGapCenter - 195268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 195268]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02892_not_prime : ¬(recordGapCenter - 195214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 195214]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02893_not_prime : ¬(recordGapCenter - 195124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 195124]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02894_not_prime : ¬(recordGapCenter - 195094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 195094]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02895_not_prime : ¬(recordGapCenter - 194758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 194758]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02896_not_prime : ¬(recordGapCenter - 194644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 194644]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02897_not_prime : ¬(recordGapCenter - 194400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 194400]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02898_not_prime : ¬(recordGapCenter - 194338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 194338]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02899_not_prime : ¬(recordGapCenter - 194254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 194254]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02900_not_prime : ¬(recordGapCenter - 194014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 194014]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02901_not_prime : ¬(recordGapCenter - 194002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 194002]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02902_not_prime : ¬(recordGapCenter - 193654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 193654]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02903_not_prime : ¬(recordGapCenter - 193594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 193594]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02904_not_prime : ¬(recordGapCenter - 193588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 193588]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02905_not_prime : ¬(recordGapCenter - 193162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 193162]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02906_not_prime : ¬(recordGapCenter - 192958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 192958]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02907_not_prime : ¬(recordGapCenter - 192772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 192772]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02908_not_prime : ¬(recordGapCenter - 192034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 192034]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02909_not_prime : ¬(recordGapCenter - 192000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 192000]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02910_not_prime : ¬(recordGapCenter - 191914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191914]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02911_not_prime : ¬(recordGapCenter - 191908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191908]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02912_not_prime : ¬(recordGapCenter - 191788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191788]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02913_not_prime : ¬(recordGapCenter - 191782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191782]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02914_not_prime : ¬(recordGapCenter - 191664).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191664]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02915_not_prime : ¬(recordGapCenter - 191578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191578]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02916_not_prime : ¬(recordGapCenter - 191524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191524]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02917_not_prime : ¬(recordGapCenter - 191242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191242]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02918_not_prime : ¬(recordGapCenter - 191194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191194]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02919_not_prime : ¬(recordGapCenter - 191188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191188]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02920_not_prime : ¬(recordGapCenter - 191098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191098]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02921_not_prime : ¬(recordGapCenter - 191062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191062]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02922_not_prime : ¬(recordGapCenter - 191014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 191014]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02923_not_prime : ¬(recordGapCenter - 190972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190972]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02924_not_prime : ¬(recordGapCenter - 190948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190948]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02925_not_prime : ¬(recordGapCenter - 190882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190882]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02926_not_prime : ¬(recordGapCenter - 190858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190858]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02927_not_prime : ¬(recordGapCenter - 190804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190804]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02928_not_prime : ¬(recordGapCenter - 190512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190512]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02929_not_prime : ¬(recordGapCenter - 190462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190462]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02930_not_prime : ¬(recordGapCenter - 190378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190378]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02931_not_prime : ¬(recordGapCenter - 190354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190354]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02932_not_prime : ¬(recordGapCenter - 190080).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190080]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02933_not_prime : ¬(recordGapCenter - 190054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 190054]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02934_not_prime : ¬(recordGapCenter - 189964).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189964]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02935_not_prime : ¬(recordGapCenter - 189922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189922]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02936_not_prime : ¬(recordGapCenter - 189814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189814]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02937_not_prime : ¬(recordGapCenter - 189724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189724]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02938_not_prime : ¬(recordGapCenter - 189454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189454]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02939_not_prime : ¬(recordGapCenter - 189418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189418]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02940_not_prime : ¬(recordGapCenter - 189298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189298]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02941_not_prime : ¬(recordGapCenter - 189268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189268]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02942_not_prime : ¬(recordGapCenter - 189172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189172]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02943_not_prime : ¬(recordGapCenter - 189118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 189118]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02944_not_prime : ¬(recordGapCenter - 188878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188878]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02945_not_prime : ¬(recordGapCenter - 188794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188794]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02946_not_prime : ¬(recordGapCenter - 188662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188662]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02947_not_prime : ¬(recordGapCenter - 188548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188548]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02948_not_prime : ¬(recordGapCenter - 188458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188458]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02949_not_prime : ¬(recordGapCenter - 188218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188218]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02950_not_prime : ¬(recordGapCenter - 188164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188164]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02951_not_prime : ¬(recordGapCenter - 188160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188160]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02952_not_prime : ¬(recordGapCenter - 188158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 188158]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02953_not_prime : ¬(recordGapCenter - 187822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 187822]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02954_not_prime : ¬(recordGapCenter - 187732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 187732]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02955_not_prime : ¬(recordGapCenter - 187522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 187522]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02956_not_prime : ¬(recordGapCenter - 187500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 187500]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02957_not_prime : ¬(recordGapCenter - 187438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 187438]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02958_not_prime : ¬(recordGapCenter - 187324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 187324]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02959_not_prime : ¬(recordGapCenter - 187084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 187084]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02960_not_prime : ¬(recordGapCenter - 186994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186994]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02961_not_prime : ¬(recordGapCenter - 186988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186988]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02962_not_prime : ¬(recordGapCenter - 186958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186958]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02963_not_prime : ¬(recordGapCenter - 186724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186724]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02964_not_prime : ¬(recordGapCenter - 186624).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186624]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02965_not_prime : ¬(recordGapCenter - 186574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186574]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02966_not_prime : ¬(recordGapCenter - 186478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186478]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02967_not_prime : ¬(recordGapCenter - 186340).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186340]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02968_not_prime : ¬(recordGapCenter - 186268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186268]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02969_not_prime : ¬(recordGapCenter - 186262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186262]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02970_not_prime : ¬(recordGapCenter - 186178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186178]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02971_not_prime : ¬(recordGapCenter - 186094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186094]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02972_not_prime : ¬(recordGapCenter - 186028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 186028]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02973_not_prime : ¬(recordGapCenter - 185908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185908]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02974_not_prime : ¬(recordGapCenter - 185884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185884]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02975_not_prime : ¬(recordGapCenter - 185842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185842]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02976_not_prime : ¬(recordGapCenter - 185698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185698]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02977_not_prime : ¬(recordGapCenter - 185404).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185404]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02978_not_prime : ¬(recordGapCenter - 185220).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185220]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02979_not_prime : ¬(recordGapCenter - 185092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185092]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02980_not_prime : ¬(recordGapCenter - 185044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 185044]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02981_not_prime : ¬(recordGapCenter - 184800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184800]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02982_not_prime : ¬(recordGapCenter - 184774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184774]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02983_not_prime : ¬(recordGapCenter - 184762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184762]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02984_not_prime : ¬(recordGapCenter - 184714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184714]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02985_not_prime : ¬(recordGapCenter - 184588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184588]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02986_not_prime : ¬(recordGapCenter - 184378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184378]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02987_not_prime : ¬(recordGapCenter - 184354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184354]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02988_not_prime : ¬(recordGapCenter - 184018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 184018]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02989_not_prime : ¬(recordGapCenter - 183994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183994]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02990_not_prime : ¬(recordGapCenter - 183934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183934]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02991_not_prime : ¬(recordGapCenter - 183750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183750]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02992_not_prime : ¬(recordGapCenter - 183622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183622]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02993_not_prime : ¬(recordGapCenter - 183412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183412]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02994_not_prime : ¬(recordGapCenter - 183382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183382]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02995_not_prime : ¬(recordGapCenter - 183262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183262]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02996_not_prime : ¬(recordGapCenter - 183028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183028]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02997_not_prime : ¬(recordGapCenter - 183004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 183004]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02998_not_prime : ¬(recordGapCenter - 182952).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182952]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm02999_not_prime : ¬(recordGapCenter - 182914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182914]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03000_not_prime : ¬(recordGapCenter - 182794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182794]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03001_not_prime : ¬(recordGapCenter - 182788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182788]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03002_not_prime : ¬(recordGapCenter - 182662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182662]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03003_not_prime : ¬(recordGapCenter - 182524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182524]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03004_not_prime : ¬(recordGapCenter - 182458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182458]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03005_not_prime : ¬(recordGapCenter - 182254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182254]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03006_not_prime : ¬(recordGapCenter - 182250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182250]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03007_not_prime : ¬(recordGapCenter - 182194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 182194]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03008_not_prime : ¬(recordGapCenter - 181942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181942]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03009_not_prime : ¬(recordGapCenter - 181894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181894]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03010_not_prime : ¬(recordGapCenter - 181822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181822]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03011_not_prime : ¬(recordGapCenter - 181642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181642]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03012_not_prime : ¬(recordGapCenter - 181444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181444]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03013_not_prime : ¬(recordGapCenter - 181348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181348]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03014_not_prime : ¬(recordGapCenter - 181318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181318]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03015_not_prime : ¬(recordGapCenter - 181234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 181234]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03016_not_prime : ¬(recordGapCenter - 180988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 180988]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03017_not_prime : ¬(recordGapCenter - 180802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 180802]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03018_not_prime : ¬(recordGapCenter - 180724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 180724]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03019_not_prime : ¬(recordGapCenter - 180394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 180394]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03020_not_prime : ¬(recordGapCenter - 180178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 180178]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03021_not_prime : ¬(recordGapCenter - 180142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 180142]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03022_not_prime : ¬(recordGapCenter - 180022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 180022]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03023_not_prime : ¬(recordGapCenter - 179878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179878]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03024_not_prime : ¬(recordGapCenter - 179818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179818]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03025_not_prime : ¬(recordGapCenter - 179794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179794]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03026_not_prime : ¬(recordGapCenter - 179734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179734]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03027_not_prime : ¬(recordGapCenter - 179668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179668]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03028_not_prime : ¬(recordGapCenter - 179638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179638]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03029_not_prime : ¬(recordGapCenter - 179548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179548]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03030_not_prime : ¬(recordGapCenter - 179200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179200]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03031_not_prime : ¬(recordGapCenter - 179188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179188]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03032_not_prime : ¬(recordGapCenter - 179092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179092]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03033_not_prime : ¬(recordGapCenter - 179038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 179038]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03034_not_prime : ¬(recordGapCenter - 178954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 178954]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03035_not_prime : ¬(recordGapCenter - 178762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 178762]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03036_not_prime : ¬(recordGapCenter - 178588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 178588]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03037_not_prime : ¬(recordGapCenter - 178378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 178378]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03038_not_prime : ¬(recordGapCenter - 178252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 178252]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03039_not_prime : ¬(recordGapCenter - 178114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 178114]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03040_not_prime : ¬(recordGapCenter - 178042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 178042]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03041_not_prime : ¬(recordGapCenter - 177870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 177870]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03042_not_prime : ¬(recordGapCenter - 177634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 177634]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03043_not_prime : ¬(recordGapCenter - 177622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 177622]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03044_not_prime : ¬(recordGapCenter - 177532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 177532]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03045_not_prime : ¬(recordGapCenter - 177408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 177408]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03046_not_prime : ¬(recordGapCenter - 176854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 176854]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03047_not_prime : ¬(recordGapCenter - 176794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 176794]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03048_not_prime : ¬(recordGapCenter - 176418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 176418]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03049_not_prime : ¬(recordGapCenter - 176284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 176284]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03050_not_prime : ¬(recordGapCenter - 176074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 176074]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03051_not_prime : ¬(recordGapCenter - 175948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175948]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03052_not_prime : ¬(recordGapCenter - 175822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175822]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03053_not_prime : ¬(recordGapCenter - 175774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175774]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03054_not_prime : ¬(recordGapCenter - 175738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175738]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03055_not_prime : ¬(recordGapCenter - 175402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175402]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03056_not_prime : ¬(recordGapCenter - 175114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175114]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03057_not_prime : ¬(recordGapCenter - 175018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175018]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03058_not_prime : ¬(recordGapCenter - 175000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 175000]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03059_not_prime : ¬(recordGapCenter - 174982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 174982]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03060_not_prime : ¬(recordGapCenter - 174604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 174604]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03061_not_prime : ¬(recordGapCenter - 174562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 174562]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03062_not_prime : ¬(recordGapCenter - 174514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 174514]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03063_not_prime : ¬(recordGapCenter - 174502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 174502]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03064_not_prime : ¬(recordGapCenter - 174358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 174358]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03065_not_prime : ¬(recordGapCenter - 174292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 174292]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03066_not_prime : ¬(recordGapCenter - 173962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173962]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03067_not_prime : ¬(recordGapCenter - 173938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173938]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03068_not_prime : ¬(recordGapCenter - 173854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173854]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03069_not_prime : ¬(recordGapCenter - 173764).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173764]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03070_not_prime : ¬(recordGapCenter - 173722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173722]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03071_not_prime : ¬(recordGapCenter - 173674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173674]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm03072_not_prime : ¬(recordGapCenter - 173284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173284]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

end PrimeFactorUnimodality
