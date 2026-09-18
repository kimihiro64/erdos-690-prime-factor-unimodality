import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00074_values : List Nat :=
  [fullRecordGapCenterValue + 186476,
    fullRecordGapCenterValue + 186482,
    fullRecordGapCenterValue + 186566,
    fullRecordGapCenterValue + 186716,
    fullRecordGapCenterValue + 186812,
    fullRecordGapCenterValue + 187028,
    fullRecordGapCenterValue + 187076,
    fullRecordGapCenterValue + 187118,
    fullRecordGapCenterValue + 187316,
    fullRecordGapCenterValue + 187500,
    fullRecordGapCenterValue + 187556,
    fullRecordGapCenterValue + 187826,
    fullRecordGapCenterValue + 188126,
    fullRecordGapCenterValue + 188160,
    fullRecordGapCenterValue + 188372,
    fullRecordGapCenterValue + 188522,
    fullRecordGapCenterValue + 188582,
    fullRecordGapCenterValue + 188588,
    fullRecordGapCenterValue + 188618,
    fullRecordGapCenterValue + 188882,
    fullRecordGapCenterValue + 188948,
    fullRecordGapCenterValue + 188966,
    fullRecordGapCenterValue + 189206,
    fullRecordGapCenterValue + 189236,
    fullRecordGapCenterValue + 189302,
    fullRecordGapCenterValue + 189446,
    fullRecordGapCenterValue + 189542,
    fullRecordGapCenterValue + 189638,
    fullRecordGapCenterValue + 189668,
    fullRecordGapCenterValue + 189698,
    fullRecordGapCenterValue + 189728,
    fullRecordGapCenterValue + 190080,
    fullRecordGapCenterValue + 190172,
    fullRecordGapCenterValue + 190262,
    fullRecordGapCenterValue + 190478,
    fullRecordGapCenterValue + 190556,
    fullRecordGapCenterValue + 190766,
    fullRecordGapCenterValue + 190886,
    fullRecordGapCenterValue + 191546,
    fullRecordGapCenterValue + 191606,
    fullRecordGapCenterValue + 191612,
    fullRecordGapCenterValue + 191732,
    fullRecordGapCenterValue + 191738,
    fullRecordGapCenterValue + 191762,
    fullRecordGapCenterValue + 191822,
    fullRecordGapCenterValue + 191852,
    fullRecordGapCenterValue + 191942,
    fullRecordGapCenterValue + 192158,
    fullRecordGapCenterValue + 192362,
    fullRecordGapCenterValue + 192456,
    fullRecordGapCenterValue + 192662,
    fullRecordGapCenterValue + 192788,
    fullRecordGapCenterValue + 192902,
    fullRecordGapCenterValue + 192938,
    fullRecordGapCenterValue + 192956,
    fullRecordGapCenterValue + 193106,
    fullRecordGapCenterValue + 193202,
    fullRecordGapCenterValue + 193322,
    fullRecordGapCenterValue + 193406,
    fullRecordGapCenterValue + 193478,
    fullRecordGapCenterValue + 193652,
    fullRecordGapCenterValue + 193748,
    fullRecordGapCenterValue + 193862,
    fullRecordGapCenterValue + 193946]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00074_fermat : ∀ n ∈ fullRecordGapRow00074_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04673_not_prime : ¬(recordGapCenter + 186476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 186476]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04674_not_prime : ¬(recordGapCenter + 186482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 186482]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04675_not_prime : ¬(recordGapCenter + 186566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 186566]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04676_not_prime : ¬(recordGapCenter + 186716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 186716]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04677_not_prime : ¬(recordGapCenter + 186812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 186812]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04678_not_prime : ¬(recordGapCenter + 187028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 187028]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04679_not_prime : ¬(recordGapCenter + 187076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 187076]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04680_not_prime : ¬(recordGapCenter + 187118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 187118]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04681_not_prime : ¬(recordGapCenter + 187316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 187316]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04682_not_prime : ¬(recordGapCenter + 187500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 187500]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04683_not_prime : ¬(recordGapCenter + 187556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 187556]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04684_not_prime : ¬(recordGapCenter + 187826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 187826]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04685_not_prime : ¬(recordGapCenter + 188126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 188126]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04686_not_prime : ¬(recordGapCenter + 188160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 188160]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04687_not_prime : ¬(recordGapCenter + 188372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 188372]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04688_not_prime : ¬(recordGapCenter + 188522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 188522]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04689_not_prime : ¬(recordGapCenter + 188582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 188582]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04690_not_prime : ¬(recordGapCenter + 188588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 188588]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04691_not_prime : ¬(recordGapCenter + 188618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 188618]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04692_not_prime : ¬(recordGapCenter + 188882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 188882]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04693_not_prime : ¬(recordGapCenter + 188948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 188948]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04694_not_prime : ¬(recordGapCenter + 188966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 188966]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04695_not_prime : ¬(recordGapCenter + 189206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 189206]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04696_not_prime : ¬(recordGapCenter + 189236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 189236]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04697_not_prime : ¬(recordGapCenter + 189302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 189302]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04698_not_prime : ¬(recordGapCenter + 189446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 189446]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04699_not_prime : ¬(recordGapCenter + 189542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 189542]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04700_not_prime : ¬(recordGapCenter + 189638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 189638]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04701_not_prime : ¬(recordGapCenter + 189668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 189668]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04702_not_prime : ¬(recordGapCenter + 189698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 189698]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04703_not_prime : ¬(recordGapCenter + 189728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 189728]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04704_not_prime : ¬(recordGapCenter + 190080).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 190080]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04705_not_prime : ¬(recordGapCenter + 190172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 190172]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04706_not_prime : ¬(recordGapCenter + 190262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 190262]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04707_not_prime : ¬(recordGapCenter + 190478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 190478]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04708_not_prime : ¬(recordGapCenter + 190556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 190556]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04709_not_prime : ¬(recordGapCenter + 190766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 190766]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04710_not_prime : ¬(recordGapCenter + 190886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 190886]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04711_not_prime : ¬(recordGapCenter + 191546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 191546]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04712_not_prime : ¬(recordGapCenter + 191606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 191606]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04713_not_prime : ¬(recordGapCenter + 191612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 191612]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04714_not_prime : ¬(recordGapCenter + 191732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 191732]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04715_not_prime : ¬(recordGapCenter + 191738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 191738]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04716_not_prime : ¬(recordGapCenter + 191762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 191762]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04717_not_prime : ¬(recordGapCenter + 191822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 191822]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04718_not_prime : ¬(recordGapCenter + 191852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 191852]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04719_not_prime : ¬(recordGapCenter + 191942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 191942]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04720_not_prime : ¬(recordGapCenter + 192158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 192158]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04721_not_prime : ¬(recordGapCenter + 192362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 192362]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04722_not_prime : ¬(recordGapCenter + 192456).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 192456]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04723_not_prime : ¬(recordGapCenter + 192662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 192662]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04724_not_prime : ¬(recordGapCenter + 192788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 192788]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04725_not_prime : ¬(recordGapCenter + 192902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 192902]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04726_not_prime : ¬(recordGapCenter + 192938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 192938]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04727_not_prime : ¬(recordGapCenter + 192956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 192956]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04728_not_prime : ¬(recordGapCenter + 193106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 193106]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04729_not_prime : ¬(recordGapCenter + 193202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 193202]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04730_not_prime : ¬(recordGapCenter + 193322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 193322]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04731_not_prime : ¬(recordGapCenter + 193406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 193406]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04732_not_prime : ¬(recordGapCenter + 193478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 193478]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04733_not_prime : ¬(recordGapCenter + 193652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 193652]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04734_not_prime : ¬(recordGapCenter + 193748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 193748]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04735_not_prime : ¬(recordGapCenter + 193862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 193862]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

theorem fullRecordGapTerm04736_not_prime : ¬(recordGapCenter + 193946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 193946]
  · apply fullRecordGapRow00074_fermat
    simp [fullRecordGapRow00074_values]

end PrimeFactorUnimodality
