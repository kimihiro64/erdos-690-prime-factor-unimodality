import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00159_values : List Nat :=
  [fullRecordGapCenterValue + 609666,
    fullRecordGapCenterValue + 609698,
    fullRecordGapCenterValue + 609758,
    fullRecordGapCenterValue + 609848,
    fullRecordGapCenterValue + 609852,
    fullRecordGapCenterValue + 609866,
    fullRecordGapCenterValue + 609962,
    fullRecordGapCenterValue + 609978,
    fullRecordGapCenterValue + 610068,
    fullRecordGapCenterValue + 610088,
    fullRecordGapCenterValue + 610106,
    fullRecordGapCenterValue + 610158,
    fullRecordGapCenterValue + 610206,
    fullRecordGapCenterValue + 610226,
    fullRecordGapCenterValue + 610262,
    fullRecordGapCenterValue + 610310,
    fullRecordGapCenterValue + 610338,
    fullRecordGapCenterValue + 610358,
    fullRecordGapCenterValue + 610422,
    fullRecordGapCenterValue + 610526,
    fullRecordGapCenterValue + 610556,
    fullRecordGapCenterValue + 610706,
    fullRecordGapCenterValue + 610778,
    fullRecordGapCenterValue + 610802,
    fullRecordGapCenterValue + 610862,
    fullRecordGapCenterValue + 610898,
    fullRecordGapCenterValue + 611012,
    fullRecordGapCenterValue + 611042,
    fullRecordGapCenterValue + 611066,
    fullRecordGapCenterValue + 611108,
    fullRecordGapCenterValue + 611126,
    fullRecordGapCenterValue + 611186,
    fullRecordGapCenterValue + 611210,
    fullRecordGapCenterValue + 611238,
    fullRecordGapCenterValue + 611346,
    fullRecordGapCenterValue + 611412,
    fullRecordGapCenterValue + 611438,
    fullRecordGapCenterValue + 611502,
    fullRecordGapCenterValue + 611628,
    fullRecordGapCenterValue + 611636,
    fullRecordGapCenterValue + 611642,
    fullRecordGapCenterValue + 611868,
    fullRecordGapCenterValue + 611922,
    fullRecordGapCenterValue + 612012,
    fullRecordGapCenterValue + 612038,
    fullRecordGapCenterValue + 612152,
    fullRecordGapCenterValue + 612182,
    fullRecordGapCenterValue + 612230,
    fullRecordGapCenterValue + 612308,
    fullRecordGapCenterValue + 612452,
    fullRecordGapCenterValue + 612488,
    fullRecordGapCenterValue + 612516,
    fullRecordGapCenterValue + 612626,
    fullRecordGapCenterValue + 612698,
    fullRecordGapCenterValue + 612732,
    fullRecordGapCenterValue + 612776,
    fullRecordGapCenterValue + 612962,
    fullRecordGapCenterValue + 613022,
    fullRecordGapCenterValue + 613046,
    fullRecordGapCenterValue + 613058,
    fullRecordGapCenterValue + 613082,
    fullRecordGapCenterValue + 613086,
    fullRecordGapCenterValue + 613148,
    fullRecordGapCenterValue + 613182]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00159_fermat : ∀ n ∈ fullRecordGapRow00159_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10113_not_prime : ¬(recordGapCenter + 609666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609666]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10114_not_prime : ¬(recordGapCenter + 609698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609698]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10115_not_prime : ¬(recordGapCenter + 609758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609758]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10116_not_prime : ¬(recordGapCenter + 609848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609848]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10117_not_prime : ¬(recordGapCenter + 609852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609852]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10118_not_prime : ¬(recordGapCenter + 609866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609866]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10119_not_prime : ¬(recordGapCenter + 609962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609962]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10120_not_prime : ¬(recordGapCenter + 609978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609978]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10121_not_prime : ¬(recordGapCenter + 610068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610068]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10122_not_prime : ¬(recordGapCenter + 610088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610088]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10123_not_prime : ¬(recordGapCenter + 610106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610106]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10124_not_prime : ¬(recordGapCenter + 610158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610158]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10125_not_prime : ¬(recordGapCenter + 610206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610206]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10126_not_prime : ¬(recordGapCenter + 610226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610226]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10127_not_prime : ¬(recordGapCenter + 610262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610262]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10128_not_prime : ¬(recordGapCenter + 610310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610310]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10129_not_prime : ¬(recordGapCenter + 610338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610338]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10130_not_prime : ¬(recordGapCenter + 610358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610358]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10131_not_prime : ¬(recordGapCenter + 610422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610422]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10132_not_prime : ¬(recordGapCenter + 610526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610526]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10133_not_prime : ¬(recordGapCenter + 610556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610556]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10134_not_prime : ¬(recordGapCenter + 610706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610706]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10135_not_prime : ¬(recordGapCenter + 610778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610778]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10136_not_prime : ¬(recordGapCenter + 610802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610802]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10137_not_prime : ¬(recordGapCenter + 610862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610862]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10138_not_prime : ¬(recordGapCenter + 610898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 610898]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10139_not_prime : ¬(recordGapCenter + 611012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611012]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10140_not_prime : ¬(recordGapCenter + 611042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611042]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10141_not_prime : ¬(recordGapCenter + 611066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611066]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10142_not_prime : ¬(recordGapCenter + 611108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611108]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10143_not_prime : ¬(recordGapCenter + 611126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611126]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10144_not_prime : ¬(recordGapCenter + 611186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611186]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10145_not_prime : ¬(recordGapCenter + 611210).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611210]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10146_not_prime : ¬(recordGapCenter + 611238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611238]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10147_not_prime : ¬(recordGapCenter + 611346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611346]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10148_not_prime : ¬(recordGapCenter + 611412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611412]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10149_not_prime : ¬(recordGapCenter + 611438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611438]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10150_not_prime : ¬(recordGapCenter + 611502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611502]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10151_not_prime : ¬(recordGapCenter + 611628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611628]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10152_not_prime : ¬(recordGapCenter + 611636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611636]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10153_not_prime : ¬(recordGapCenter + 611642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611642]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10154_not_prime : ¬(recordGapCenter + 611868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611868]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10155_not_prime : ¬(recordGapCenter + 611922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 611922]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10156_not_prime : ¬(recordGapCenter + 612012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 612012]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10157_not_prime : ¬(recordGapCenter + 612038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 612038]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10158_not_prime : ¬(recordGapCenter + 612152).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 612152]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10159_not_prime : ¬(recordGapCenter + 612182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 612182]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10160_not_prime : ¬(recordGapCenter + 612230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 612230]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10161_not_prime : ¬(recordGapCenter + 612308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 612308]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10162_not_prime : ¬(recordGapCenter + 612452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 612452]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10163_not_prime : ¬(recordGapCenter + 612488).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 612488]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10164_not_prime : ¬(recordGapCenter + 612516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 612516]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10165_not_prime : ¬(recordGapCenter + 612626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 612626]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10166_not_prime : ¬(recordGapCenter + 612698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 612698]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10167_not_prime : ¬(recordGapCenter + 612732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 612732]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10168_not_prime : ¬(recordGapCenter + 612776).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 612776]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10169_not_prime : ¬(recordGapCenter + 612962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 612962]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10170_not_prime : ¬(recordGapCenter + 613022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613022]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10171_not_prime : ¬(recordGapCenter + 613046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613046]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10172_not_prime : ¬(recordGapCenter + 613058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613058]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10173_not_prime : ¬(recordGapCenter + 613082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613082]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10174_not_prime : ¬(recordGapCenter + 613086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613086]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10175_not_prime : ¬(recordGapCenter + 613148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613148]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

theorem fullRecordGapTerm10176_not_prime : ¬(recordGapCenter + 613182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613182]
  · apply fullRecordGapRow00159_fermat
    simp [fullRecordGapRow00159_values]

end PrimeFactorUnimodality
