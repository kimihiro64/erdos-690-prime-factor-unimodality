import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00117_values : List Nat :=
  [fullRecordGapCenterValue + 427796,
    fullRecordGapCenterValue + 427886,
    fullRecordGapCenterValue + 427998,
    fullRecordGapCenterValue + 428018,
    fullRecordGapCenterValue + 428066,
    fullRecordGapCenterValue + 428082,
    fullRecordGapCenterValue + 428102,
    fullRecordGapCenterValue + 428118,
    fullRecordGapCenterValue + 428132,
    fullRecordGapCenterValue + 428216,
    fullRecordGapCenterValue + 428228,
    fullRecordGapCenterValue + 428258,
    fullRecordGapCenterValue + 428276,
    fullRecordGapCenterValue + 428282,
    fullRecordGapCenterValue + 428396,
    fullRecordGapCenterValue + 428426,
    fullRecordGapCenterValue + 428438,
    fullRecordGapCenterValue + 428486,
    fullRecordGapCenterValue + 428652,
    fullRecordGapCenterValue + 428762,
    fullRecordGapCenterValue + 428838,
    fullRecordGapCenterValue + 428888,
    fullRecordGapCenterValue + 428898,
    fullRecordGapCenterValue + 429038,
    fullRecordGapCenterValue + 429356,
    fullRecordGapCenterValue + 429558,
    fullRecordGapCenterValue + 429578,
    fullRecordGapCenterValue + 429698,
    fullRecordGapCenterValue + 429752,
    fullRecordGapCenterValue + 429782,
    fullRecordGapCenterValue + 429882,
    fullRecordGapCenterValue + 429978,
    fullRecordGapCenterValue + 430158,
    fullRecordGapCenterValue + 430242,
    fullRecordGapCenterValue + 430266,
    fullRecordGapCenterValue + 430278,
    fullRecordGapCenterValue + 430286,
    fullRecordGapCenterValue + 430328,
    fullRecordGapCenterValue + 430446,
    fullRecordGapCenterValue + 430662,
    fullRecordGapCenterValue + 430706,
    fullRecordGapCenterValue + 430796,
    fullRecordGapCenterValue + 430886,
    fullRecordGapCenterValue + 430922,
    fullRecordGapCenterValue + 430988,
    fullRecordGapCenterValue + 431058,
    fullRecordGapCenterValue + 431286,
    fullRecordGapCenterValue + 431322,
    fullRecordGapCenterValue + 431336,
    fullRecordGapCenterValue + 431502,
    fullRecordGapCenterValue + 431666,
    fullRecordGapCenterValue + 431672,
    fullRecordGapCenterValue + 431778,
    fullRecordGapCenterValue + 431798,
    fullRecordGapCenterValue + 431826,
    fullRecordGapCenterValue + 432008,
    fullRecordGapCenterValue + 432392,
    fullRecordGapCenterValue + 432462,
    fullRecordGapCenterValue + 432518,
    fullRecordGapCenterValue + 432716,
    fullRecordGapCenterValue + 432728,
    fullRecordGapCenterValue + 432902,
    fullRecordGapCenterValue + 432962,
    fullRecordGapCenterValue + 432968]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00117_fermat : ∀ n ∈ fullRecordGapRow00117_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07425_not_prime : ¬(recordGapCenter + 427796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 427796]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07426_not_prime : ¬(recordGapCenter + 427886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 427886]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07427_not_prime : ¬(recordGapCenter + 427998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 427998]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07428_not_prime : ¬(recordGapCenter + 428018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428018]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07429_not_prime : ¬(recordGapCenter + 428066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428066]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07430_not_prime : ¬(recordGapCenter + 428082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428082]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07431_not_prime : ¬(recordGapCenter + 428102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428102]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07432_not_prime : ¬(recordGapCenter + 428118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428118]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07433_not_prime : ¬(recordGapCenter + 428132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428132]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07434_not_prime : ¬(recordGapCenter + 428216).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428216]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07435_not_prime : ¬(recordGapCenter + 428228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428228]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07436_not_prime : ¬(recordGapCenter + 428258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428258]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07437_not_prime : ¬(recordGapCenter + 428276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428276]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07438_not_prime : ¬(recordGapCenter + 428282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428282]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07439_not_prime : ¬(recordGapCenter + 428396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428396]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07440_not_prime : ¬(recordGapCenter + 428426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428426]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07441_not_prime : ¬(recordGapCenter + 428438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428438]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07442_not_prime : ¬(recordGapCenter + 428486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428486]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07443_not_prime : ¬(recordGapCenter + 428652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428652]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07444_not_prime : ¬(recordGapCenter + 428762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428762]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07445_not_prime : ¬(recordGapCenter + 428838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428838]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07446_not_prime : ¬(recordGapCenter + 428888).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428888]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07447_not_prime : ¬(recordGapCenter + 428898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 428898]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07448_not_prime : ¬(recordGapCenter + 429038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 429038]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07449_not_prime : ¬(recordGapCenter + 429356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 429356]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07450_not_prime : ¬(recordGapCenter + 429558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 429558]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07451_not_prime : ¬(recordGapCenter + 429578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 429578]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07452_not_prime : ¬(recordGapCenter + 429698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 429698]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07453_not_prime : ¬(recordGapCenter + 429752).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 429752]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07454_not_prime : ¬(recordGapCenter + 429782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 429782]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07455_not_prime : ¬(recordGapCenter + 429882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 429882]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07456_not_prime : ¬(recordGapCenter + 429978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 429978]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07457_not_prime : ¬(recordGapCenter + 430158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 430158]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07458_not_prime : ¬(recordGapCenter + 430242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 430242]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07459_not_prime : ¬(recordGapCenter + 430266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 430266]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07460_not_prime : ¬(recordGapCenter + 430278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 430278]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07461_not_prime : ¬(recordGapCenter + 430286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 430286]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07462_not_prime : ¬(recordGapCenter + 430328).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 430328]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07463_not_prime : ¬(recordGapCenter + 430446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 430446]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07464_not_prime : ¬(recordGapCenter + 430662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 430662]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07465_not_prime : ¬(recordGapCenter + 430706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 430706]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07466_not_prime : ¬(recordGapCenter + 430796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 430796]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07467_not_prime : ¬(recordGapCenter + 430886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 430886]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07468_not_prime : ¬(recordGapCenter + 430922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 430922]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07469_not_prime : ¬(recordGapCenter + 430988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 430988]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07470_not_prime : ¬(recordGapCenter + 431058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 431058]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07471_not_prime : ¬(recordGapCenter + 431286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 431286]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07472_not_prime : ¬(recordGapCenter + 431322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 431322]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07473_not_prime : ¬(recordGapCenter + 431336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 431336]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07474_not_prime : ¬(recordGapCenter + 431502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 431502]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07475_not_prime : ¬(recordGapCenter + 431666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 431666]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07476_not_prime : ¬(recordGapCenter + 431672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 431672]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07477_not_prime : ¬(recordGapCenter + 431778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 431778]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07478_not_prime : ¬(recordGapCenter + 431798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 431798]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07479_not_prime : ¬(recordGapCenter + 431826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 431826]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07480_not_prime : ¬(recordGapCenter + 432008).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 432008]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07481_not_prime : ¬(recordGapCenter + 432392).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 432392]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07482_not_prime : ¬(recordGapCenter + 432462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 432462]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07483_not_prime : ¬(recordGapCenter + 432518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 432518]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07484_not_prime : ¬(recordGapCenter + 432716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 432716]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07485_not_prime : ¬(recordGapCenter + 432728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 432728]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07486_not_prime : ¬(recordGapCenter + 432902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 432902]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07487_not_prime : ¬(recordGapCenter + 432962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 432962]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

theorem fullRecordGapTerm07488_not_prime : ¬(recordGapCenter + 432968).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 432968]
  · apply fullRecordGapRow00117_fermat
    simp [fullRecordGapRow00117_values]

end PrimeFactorUnimodality
