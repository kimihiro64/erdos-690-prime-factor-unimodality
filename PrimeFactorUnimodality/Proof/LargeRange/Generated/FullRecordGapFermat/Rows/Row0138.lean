import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00138_values : List Nat :=
  [fullRecordGapCenterValue + 525038,
    fullRecordGapCenterValue + 525068,
    fullRecordGapCenterValue + 525102,
    fullRecordGapCenterValue + 525108,
    fullRecordGapCenterValue + 525110,
    fullRecordGapCenterValue + 525138,
    fullRecordGapCenterValue + 525170,
    fullRecordGapCenterValue + 525176,
    fullRecordGapCenterValue + 525282,
    fullRecordGapCenterValue + 525302,
    fullRecordGapCenterValue + 525318,
    fullRecordGapCenterValue + 525362,
    fullRecordGapCenterValue + 525372,
    fullRecordGapCenterValue + 525386,
    fullRecordGapCenterValue + 525396,
    fullRecordGapCenterValue + 525410,
    fullRecordGapCenterValue + 525446,
    fullRecordGapCenterValue + 525452,
    fullRecordGapCenterValue + 525498,
    fullRecordGapCenterValue + 525612,
    fullRecordGapCenterValue + 525656,
    fullRecordGapCenterValue + 525738,
    fullRecordGapCenterValue + 525786,
    fullRecordGapCenterValue + 525788,
    fullRecordGapCenterValue + 525830,
    fullRecordGapCenterValue + 525848,
    fullRecordGapCenterValue + 525956,
    fullRecordGapCenterValue + 526088,
    fullRecordGapCenterValue + 526142,
    fullRecordGapCenterValue + 526146,
    fullRecordGapCenterValue + 526206,
    fullRecordGapCenterValue + 526418,
    fullRecordGapCenterValue + 526472,
    fullRecordGapCenterValue + 526646,
    fullRecordGapCenterValue + 526670,
    fullRecordGapCenterValue + 526692,
    fullRecordGapCenterValue + 526712,
    fullRecordGapCenterValue + 526730,
    fullRecordGapCenterValue + 526766,
    fullRecordGapCenterValue + 526818,
    fullRecordGapCenterValue + 526848,
    fullRecordGapCenterValue + 527066,
    fullRecordGapCenterValue + 527090,
    fullRecordGapCenterValue + 527210,
    fullRecordGapCenterValue + 527222,
    fullRecordGapCenterValue + 527286,
    fullRecordGapCenterValue + 527348,
    fullRecordGapCenterValue + 527396,
    fullRecordGapCenterValue + 527570,
    fullRecordGapCenterValue + 527636,
    fullRecordGapCenterValue + 527658,
    fullRecordGapCenterValue + 527676,
    fullRecordGapCenterValue + 527726,
    fullRecordGapCenterValue + 527756,
    fullRecordGapCenterValue + 527762,
    fullRecordGapCenterValue + 527838,
    fullRecordGapCenterValue + 527882,
    fullRecordGapCenterValue + 527892,
    fullRecordGapCenterValue + 527966,
    fullRecordGapCenterValue + 528000,
    fullRecordGapCenterValue + 528006,
    fullRecordGapCenterValue + 528182,
    fullRecordGapCenterValue + 528188,
    fullRecordGapCenterValue + 528252]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00138_fermat : ∀ n ∈ fullRecordGapRow00138_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08769_not_prime : ¬(recordGapCenter + 525038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525038]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08770_not_prime : ¬(recordGapCenter + 525068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525068]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08771_not_prime : ¬(recordGapCenter + 525102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525102]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08772_not_prime : ¬(recordGapCenter + 525108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525108]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08773_not_prime : ¬(recordGapCenter + 525110).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525110]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08774_not_prime : ¬(recordGapCenter + 525138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525138]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08775_not_prime : ¬(recordGapCenter + 525170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525170]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08776_not_prime : ¬(recordGapCenter + 525176).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525176]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08777_not_prime : ¬(recordGapCenter + 525282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525282]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08778_not_prime : ¬(recordGapCenter + 525302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525302]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08779_not_prime : ¬(recordGapCenter + 525318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525318]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08780_not_prime : ¬(recordGapCenter + 525362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525362]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08781_not_prime : ¬(recordGapCenter + 525372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525372]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08782_not_prime : ¬(recordGapCenter + 525386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525386]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08783_not_prime : ¬(recordGapCenter + 525396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525396]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08784_not_prime : ¬(recordGapCenter + 525410).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525410]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08785_not_prime : ¬(recordGapCenter + 525446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525446]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08786_not_prime : ¬(recordGapCenter + 525452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525452]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08787_not_prime : ¬(recordGapCenter + 525498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525498]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08788_not_prime : ¬(recordGapCenter + 525612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525612]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08789_not_prime : ¬(recordGapCenter + 525656).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525656]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08790_not_prime : ¬(recordGapCenter + 525738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525738]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08791_not_prime : ¬(recordGapCenter + 525786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525786]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08792_not_prime : ¬(recordGapCenter + 525788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525788]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08793_not_prime : ¬(recordGapCenter + 525830).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525830]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08794_not_prime : ¬(recordGapCenter + 525848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525848]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08795_not_prime : ¬(recordGapCenter + 525956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525956]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08796_not_prime : ¬(recordGapCenter + 526088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 526088]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08797_not_prime : ¬(recordGapCenter + 526142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 526142]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08798_not_prime : ¬(recordGapCenter + 526146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 526146]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08799_not_prime : ¬(recordGapCenter + 526206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 526206]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08800_not_prime : ¬(recordGapCenter + 526418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 526418]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08801_not_prime : ¬(recordGapCenter + 526472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 526472]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08802_not_prime : ¬(recordGapCenter + 526646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 526646]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08803_not_prime : ¬(recordGapCenter + 526670).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 526670]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08804_not_prime : ¬(recordGapCenter + 526692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 526692]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08805_not_prime : ¬(recordGapCenter + 526712).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 526712]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08806_not_prime : ¬(recordGapCenter + 526730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 526730]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08807_not_prime : ¬(recordGapCenter + 526766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 526766]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08808_not_prime : ¬(recordGapCenter + 526818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 526818]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08809_not_prime : ¬(recordGapCenter + 526848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 526848]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08810_not_prime : ¬(recordGapCenter + 527066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527066]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08811_not_prime : ¬(recordGapCenter + 527090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527090]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08812_not_prime : ¬(recordGapCenter + 527210).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527210]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08813_not_prime : ¬(recordGapCenter + 527222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527222]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08814_not_prime : ¬(recordGapCenter + 527286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527286]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08815_not_prime : ¬(recordGapCenter + 527348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527348]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08816_not_prime : ¬(recordGapCenter + 527396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527396]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08817_not_prime : ¬(recordGapCenter + 527570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527570]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08818_not_prime : ¬(recordGapCenter + 527636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527636]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08819_not_prime : ¬(recordGapCenter + 527658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527658]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08820_not_prime : ¬(recordGapCenter + 527676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527676]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08821_not_prime : ¬(recordGapCenter + 527726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527726]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08822_not_prime : ¬(recordGapCenter + 527756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527756]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08823_not_prime : ¬(recordGapCenter + 527762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527762]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08824_not_prime : ¬(recordGapCenter + 527838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527838]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08825_not_prime : ¬(recordGapCenter + 527882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527882]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08826_not_prime : ¬(recordGapCenter + 527892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527892]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08827_not_prime : ¬(recordGapCenter + 527966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 527966]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08828_not_prime : ¬(recordGapCenter + 528000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 528000]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08829_not_prime : ¬(recordGapCenter + 528006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 528006]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08830_not_prime : ¬(recordGapCenter + 528182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 528182]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08831_not_prime : ¬(recordGapCenter + 528188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 528188]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

theorem fullRecordGapTerm08832_not_prime : ¬(recordGapCenter + 528252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 528252]
  · apply fullRecordGapRow00138_fermat
    simp [fullRecordGapRow00138_values]

end PrimeFactorUnimodality
