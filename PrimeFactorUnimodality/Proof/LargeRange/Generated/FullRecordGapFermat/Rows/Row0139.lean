import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00139_values : List Nat :=
  [fullRecordGapCenterValue + 528278,
    fullRecordGapCenterValue + 528566,
    fullRecordGapCenterValue + 528662,
    fullRecordGapCenterValue + 528698,
    fullRecordGapCenterValue + 528872,
    fullRecordGapCenterValue + 529062,
    fullRecordGapCenterValue + 529106,
    fullRecordGapCenterValue + 529190,
    fullRecordGapCenterValue + 529200,
    fullRecordGapCenterValue + 529212,
    fullRecordGapCenterValue + 529422,
    fullRecordGapCenterValue + 529428,
    fullRecordGapCenterValue + 529446,
    fullRecordGapCenterValue + 529526,
    fullRecordGapCenterValue + 529548,
    fullRecordGapCenterValue + 529566,
    fullRecordGapCenterValue + 529572,
    fullRecordGapCenterValue + 529658,
    fullRecordGapCenterValue + 529730,
    fullRecordGapCenterValue + 529742,
    fullRecordGapCenterValue + 529748,
    fullRecordGapCenterValue + 529862,
    fullRecordGapCenterValue + 529898,
    fullRecordGapCenterValue + 529908,
    fullRecordGapCenterValue + 529926,
    fullRecordGapCenterValue + 529982,
    fullRecordGapCenterValue + 530148,
    fullRecordGapCenterValue + 530268,
    fullRecordGapCenterValue + 530408,
    fullRecordGapCenterValue + 530436,
    fullRecordGapCenterValue + 530492,
    fullRecordGapCenterValue + 530546,
    fullRecordGapCenterValue + 530562,
    fullRecordGapCenterValue + 530588,
    fullRecordGapCenterValue + 530652,
    fullRecordGapCenterValue + 530666,
    fullRecordGapCenterValue + 530762,
    fullRecordGapCenterValue + 530846,
    fullRecordGapCenterValue + 530888,
    fullRecordGapCenterValue + 530918,
    fullRecordGapCenterValue + 530930,
    fullRecordGapCenterValue + 531078,
    fullRecordGapCenterValue + 531122,
    fullRecordGapCenterValue + 531170,
    fullRecordGapCenterValue + 531242,
    fullRecordGapCenterValue + 531458,
    fullRecordGapCenterValue + 531470,
    fullRecordGapCenterValue + 531546,
    fullRecordGapCenterValue + 531548,
    fullRecordGapCenterValue + 531638,
    fullRecordGapCenterValue + 531722,
    fullRecordGapCenterValue + 531746,
    fullRecordGapCenterValue + 531906,
    fullRecordGapCenterValue + 531966,
    fullRecordGapCenterValue + 532002,
    fullRecordGapCenterValue + 532010,
    fullRecordGapCenterValue + 532106,
    fullRecordGapCenterValue + 532212,
    fullRecordGapCenterValue + 532310,
    fullRecordGapCenterValue + 532326,
    fullRecordGapCenterValue + 532388,
    fullRecordGapCenterValue + 532400,
    fullRecordGapCenterValue + 532436,
    fullRecordGapCenterValue + 532442]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00139_fermat : ∀ n ∈ fullRecordGapRow00139_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08833_not_prime : ¬(recordGapCenter + 528278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 528278]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08834_not_prime : ¬(recordGapCenter + 528566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 528566]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08835_not_prime : ¬(recordGapCenter + 528662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 528662]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08836_not_prime : ¬(recordGapCenter + 528698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 528698]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08837_not_prime : ¬(recordGapCenter + 528872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 528872]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08838_not_prime : ¬(recordGapCenter + 529062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529062]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08839_not_prime : ¬(recordGapCenter + 529106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529106]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08840_not_prime : ¬(recordGapCenter + 529190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529190]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08841_not_prime : ¬(recordGapCenter + 529200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529200]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08842_not_prime : ¬(recordGapCenter + 529212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529212]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08843_not_prime : ¬(recordGapCenter + 529422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529422]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08844_not_prime : ¬(recordGapCenter + 529428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529428]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08845_not_prime : ¬(recordGapCenter + 529446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529446]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08846_not_prime : ¬(recordGapCenter + 529526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529526]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08847_not_prime : ¬(recordGapCenter + 529548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529548]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08848_not_prime : ¬(recordGapCenter + 529566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529566]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08849_not_prime : ¬(recordGapCenter + 529572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529572]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08850_not_prime : ¬(recordGapCenter + 529658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529658]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08851_not_prime : ¬(recordGapCenter + 529730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529730]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08852_not_prime : ¬(recordGapCenter + 529742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529742]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08853_not_prime : ¬(recordGapCenter + 529748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529748]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08854_not_prime : ¬(recordGapCenter + 529862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529862]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08855_not_prime : ¬(recordGapCenter + 529898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529898]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08856_not_prime : ¬(recordGapCenter + 529908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529908]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08857_not_prime : ¬(recordGapCenter + 529926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529926]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08858_not_prime : ¬(recordGapCenter + 529982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 529982]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08859_not_prime : ¬(recordGapCenter + 530148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530148]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08860_not_prime : ¬(recordGapCenter + 530268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530268]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08861_not_prime : ¬(recordGapCenter + 530408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530408]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08862_not_prime : ¬(recordGapCenter + 530436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530436]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08863_not_prime : ¬(recordGapCenter + 530492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530492]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08864_not_prime : ¬(recordGapCenter + 530546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530546]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08865_not_prime : ¬(recordGapCenter + 530562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530562]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08866_not_prime : ¬(recordGapCenter + 530588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530588]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08867_not_prime : ¬(recordGapCenter + 530652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530652]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08868_not_prime : ¬(recordGapCenter + 530666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530666]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08869_not_prime : ¬(recordGapCenter + 530762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530762]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08870_not_prime : ¬(recordGapCenter + 530846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530846]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08871_not_prime : ¬(recordGapCenter + 530888).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530888]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08872_not_prime : ¬(recordGapCenter + 530918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530918]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08873_not_prime : ¬(recordGapCenter + 530930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 530930]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08874_not_prime : ¬(recordGapCenter + 531078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 531078]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08875_not_prime : ¬(recordGapCenter + 531122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 531122]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08876_not_prime : ¬(recordGapCenter + 531170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 531170]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08877_not_prime : ¬(recordGapCenter + 531242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 531242]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08878_not_prime : ¬(recordGapCenter + 531458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 531458]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08879_not_prime : ¬(recordGapCenter + 531470).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 531470]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08880_not_prime : ¬(recordGapCenter + 531546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 531546]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08881_not_prime : ¬(recordGapCenter + 531548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 531548]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08882_not_prime : ¬(recordGapCenter + 531638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 531638]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08883_not_prime : ¬(recordGapCenter + 531722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 531722]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08884_not_prime : ¬(recordGapCenter + 531746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 531746]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08885_not_prime : ¬(recordGapCenter + 531906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 531906]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08886_not_prime : ¬(recordGapCenter + 531966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 531966]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08887_not_prime : ¬(recordGapCenter + 532002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532002]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08888_not_prime : ¬(recordGapCenter + 532010).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532010]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08889_not_prime : ¬(recordGapCenter + 532106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532106]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08890_not_prime : ¬(recordGapCenter + 532212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532212]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08891_not_prime : ¬(recordGapCenter + 532310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532310]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08892_not_prime : ¬(recordGapCenter + 532326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532326]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08893_not_prime : ¬(recordGapCenter + 532388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532388]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08894_not_prime : ¬(recordGapCenter + 532400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532400]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08895_not_prime : ¬(recordGapCenter + 532436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532436]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

theorem fullRecordGapTerm08896_not_prime : ¬(recordGapCenter + 532442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532442]
  · apply fullRecordGapRow00139_fermat
    simp [fullRecordGapRow00139_values]

end PrimeFactorUnimodality
