import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00104_values : List Nat :=
  [fullRecordGapCenterValue + 363578,
    fullRecordGapCenterValue + 363606,
    fullRecordGapCenterValue + 363702,
    fullRecordGapCenterValue + 363738,
    fullRecordGapCenterValue + 363746,
    fullRecordGapCenterValue + 363806,
    fullRecordGapCenterValue + 363882,
    fullRecordGapCenterValue + 363956,
    fullRecordGapCenterValue + 364022,
    fullRecordGapCenterValue + 364082,
    fullRecordGapCenterValue + 364218,
    fullRecordGapCenterValue + 364262,
    fullRecordGapCenterValue + 364358,
    fullRecordGapCenterValue + 364478,
    fullRecordGapCenterValue + 364500,
    fullRecordGapCenterValue + 364556,
    fullRecordGapCenterValue + 364578,
    fullRecordGapCenterValue + 364652,
    fullRecordGapCenterValue + 364758,
    fullRecordGapCenterValue + 364772,
    fullRecordGapCenterValue + 364946,
    fullRecordGapCenterValue + 365018,
    fullRecordGapCenterValue + 365198,
    fullRecordGapCenterValue + 365282,
    fullRecordGapCenterValue + 365426,
    fullRecordGapCenterValue + 365478,
    fullRecordGapCenterValue + 365492,
    fullRecordGapCenterValue + 365558,
    fullRecordGapCenterValue + 365576,
    fullRecordGapCenterValue + 365622,
    fullRecordGapCenterValue + 365642,
    fullRecordGapCenterValue + 365678,
    fullRecordGapCenterValue + 365828,
    fullRecordGapCenterValue + 365858,
    fullRecordGapCenterValue + 365996,
    fullRecordGapCenterValue + 366006,
    fullRecordGapCenterValue + 366182,
    fullRecordGapCenterValue + 366258,
    fullRecordGapCenterValue + 366332,
    fullRecordGapCenterValue + 366342,
    fullRecordGapCenterValue + 366518,
    fullRecordGapCenterValue + 366566,
    fullRecordGapCenterValue + 366578,
    fullRecordGapCenterValue + 366602,
    fullRecordGapCenterValue + 366686,
    fullRecordGapCenterValue + 366746,
    fullRecordGapCenterValue + 366812,
    fullRecordGapCenterValue + 366902,
    fullRecordGapCenterValue + 366998,
    fullRecordGapCenterValue + 367266,
    fullRecordGapCenterValue + 367322,
    fullRecordGapCenterValue + 367416,
    fullRecordGapCenterValue + 367518,
    fullRecordGapCenterValue + 367782,
    fullRecordGapCenterValue + 367838,
    fullRecordGapCenterValue + 367986,
    fullRecordGapCenterValue + 368006,
    fullRecordGapCenterValue + 368036,
    fullRecordGapCenterValue + 368162,
    fullRecordGapCenterValue + 368168,
    fullRecordGapCenterValue + 368216,
    fullRecordGapCenterValue + 368418,
    fullRecordGapCenterValue + 368546,
    fullRecordGapCenterValue + 368558]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00104_fermat : ∀ n ∈ fullRecordGapRow00104_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06593_not_prime : ¬(recordGapCenter + 363578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363578]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06594_not_prime : ¬(recordGapCenter + 363606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363606]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06595_not_prime : ¬(recordGapCenter + 363702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363702]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06596_not_prime : ¬(recordGapCenter + 363738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363738]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06597_not_prime : ¬(recordGapCenter + 363746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363746]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06598_not_prime : ¬(recordGapCenter + 363806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363806]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06599_not_prime : ¬(recordGapCenter + 363882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363882]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06600_not_prime : ¬(recordGapCenter + 363956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363956]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06601_not_prime : ¬(recordGapCenter + 364022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364022]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06602_not_prime : ¬(recordGapCenter + 364082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364082]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06603_not_prime : ¬(recordGapCenter + 364218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364218]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06604_not_prime : ¬(recordGapCenter + 364262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364262]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06605_not_prime : ¬(recordGapCenter + 364358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364358]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06606_not_prime : ¬(recordGapCenter + 364478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364478]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06607_not_prime : ¬(recordGapCenter + 364500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364500]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06608_not_prime : ¬(recordGapCenter + 364556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364556]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06609_not_prime : ¬(recordGapCenter + 364578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364578]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06610_not_prime : ¬(recordGapCenter + 364652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364652]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06611_not_prime : ¬(recordGapCenter + 364758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364758]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06612_not_prime : ¬(recordGapCenter + 364772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364772]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06613_not_prime : ¬(recordGapCenter + 364946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 364946]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06614_not_prime : ¬(recordGapCenter + 365018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365018]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06615_not_prime : ¬(recordGapCenter + 365198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365198]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06616_not_prime : ¬(recordGapCenter + 365282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365282]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06617_not_prime : ¬(recordGapCenter + 365426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365426]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06618_not_prime : ¬(recordGapCenter + 365478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365478]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06619_not_prime : ¬(recordGapCenter + 365492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365492]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06620_not_prime : ¬(recordGapCenter + 365558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365558]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06621_not_prime : ¬(recordGapCenter + 365576).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365576]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06622_not_prime : ¬(recordGapCenter + 365622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365622]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06623_not_prime : ¬(recordGapCenter + 365642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365642]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06624_not_prime : ¬(recordGapCenter + 365678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365678]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06625_not_prime : ¬(recordGapCenter + 365828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365828]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06626_not_prime : ¬(recordGapCenter + 365858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365858]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06627_not_prime : ¬(recordGapCenter + 365996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 365996]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06628_not_prime : ¬(recordGapCenter + 366006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366006]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06629_not_prime : ¬(recordGapCenter + 366182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366182]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06630_not_prime : ¬(recordGapCenter + 366258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366258]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06631_not_prime : ¬(recordGapCenter + 366332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366332]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06632_not_prime : ¬(recordGapCenter + 366342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366342]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06633_not_prime : ¬(recordGapCenter + 366518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366518]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06634_not_prime : ¬(recordGapCenter + 366566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366566]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06635_not_prime : ¬(recordGapCenter + 366578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366578]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06636_not_prime : ¬(recordGapCenter + 366602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366602]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06637_not_prime : ¬(recordGapCenter + 366686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366686]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06638_not_prime : ¬(recordGapCenter + 366746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366746]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06639_not_prime : ¬(recordGapCenter + 366812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366812]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06640_not_prime : ¬(recordGapCenter + 366902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366902]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06641_not_prime : ¬(recordGapCenter + 366998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 366998]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06642_not_prime : ¬(recordGapCenter + 367266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 367266]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06643_not_prime : ¬(recordGapCenter + 367322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 367322]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06644_not_prime : ¬(recordGapCenter + 367416).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 367416]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06645_not_prime : ¬(recordGapCenter + 367518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 367518]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06646_not_prime : ¬(recordGapCenter + 367782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 367782]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06647_not_prime : ¬(recordGapCenter + 367838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 367838]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06648_not_prime : ¬(recordGapCenter + 367986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 367986]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06649_not_prime : ¬(recordGapCenter + 368006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368006]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06650_not_prime : ¬(recordGapCenter + 368036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368036]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06651_not_prime : ¬(recordGapCenter + 368162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368162]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06652_not_prime : ¬(recordGapCenter + 368168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368168]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06653_not_prime : ¬(recordGapCenter + 368216).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368216]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06654_not_prime : ¬(recordGapCenter + 368418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368418]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06655_not_prime : ¬(recordGapCenter + 368546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368546]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

theorem fullRecordGapTerm06656_not_prime : ¬(recordGapCenter + 368558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368558]
  · apply fullRecordGapRow00104_fermat
    simp [fullRecordGapRow00104_values]

end PrimeFactorUnimodality
