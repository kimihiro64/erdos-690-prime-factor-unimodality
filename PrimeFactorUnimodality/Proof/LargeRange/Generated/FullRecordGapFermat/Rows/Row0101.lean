import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00101_values : List Nat :=
  [fullRecordGapCenterValue + 348482,
    fullRecordGapCenterValue + 348632,
    fullRecordGapCenterValue + 348666,
    fullRecordGapCenterValue + 348716,
    fullRecordGapCenterValue + 348882,
    fullRecordGapCenterValue + 349142,
    fullRecordGapCenterValue + 349196,
    fullRecordGapCenterValue + 349242,
    fullRecordGapCenterValue + 349266,
    fullRecordGapCenterValue + 349298,
    fullRecordGapCenterValue + 349352,
    fullRecordGapCenterValue + 349358,
    fullRecordGapCenterValue + 349386,
    fullRecordGapCenterValue + 349458,
    fullRecordGapCenterValue + 349626,
    fullRecordGapCenterValue + 349658,
    fullRecordGapCenterValue + 349718,
    fullRecordGapCenterValue + 349736,
    fullRecordGapCenterValue + 349886,
    fullRecordGapCenterValue + 349920,
    fullRecordGapCenterValue + 349926,
    fullRecordGapCenterValue + 350000,
    fullRecordGapCenterValue + 350072,
    fullRecordGapCenterValue + 350156,
    fullRecordGapCenterValue + 350282,
    fullRecordGapCenterValue + 350312,
    fullRecordGapCenterValue + 350408,
    fullRecordGapCenterValue + 350418,
    fullRecordGapCenterValue + 350466,
    fullRecordGapCenterValue + 350502,
    fullRecordGapCenterValue + 350562,
    fullRecordGapCenterValue + 350582,
    fullRecordGapCenterValue + 350666,
    fullRecordGapCenterValue + 350862,
    fullRecordGapCenterValue + 350876,
    fullRecordGapCenterValue + 350936,
    fullRecordGapCenterValue + 351066,
    fullRecordGapCenterValue + 351146,
    fullRecordGapCenterValue + 351188,
    fullRecordGapCenterValue + 351222,
    fullRecordGapCenterValue + 351326,
    fullRecordGapCenterValue + 351332,
    fullRecordGapCenterValue + 351398,
    fullRecordGapCenterValue + 351506,
    fullRecordGapCenterValue + 351782,
    fullRecordGapCenterValue + 351836,
    fullRecordGapCenterValue + 351942,
    fullRecordGapCenterValue + 352046,
    fullRecordGapCenterValue + 352076,
    fullRecordGapCenterValue + 352082,
    fullRecordGapCenterValue + 352122,
    fullRecordGapCenterValue + 352158,
    fullRecordGapCenterValue + 352266,
    fullRecordGapCenterValue + 352322,
    fullRecordGapCenterValue + 352382,
    fullRecordGapCenterValue + 352398,
    fullRecordGapCenterValue + 352472,
    fullRecordGapCenterValue + 352542,
    fullRecordGapCenterValue + 352626,
    fullRecordGapCenterValue + 352800,
    fullRecordGapCenterValue + 352808,
    fullRecordGapCenterValue + 352892,
    fullRecordGapCenterValue + 352952,
    fullRecordGapCenterValue + 353018]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00101_fermat : ∀ n ∈ fullRecordGapRow00101_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06401_not_prime : ¬(recordGapCenter + 348482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348482]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06402_not_prime : ¬(recordGapCenter + 348632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348632]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06403_not_prime : ¬(recordGapCenter + 348666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348666]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06404_not_prime : ¬(recordGapCenter + 348716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348716]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06405_not_prime : ¬(recordGapCenter + 348882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348882]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06406_not_prime : ¬(recordGapCenter + 349142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349142]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06407_not_prime : ¬(recordGapCenter + 349196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349196]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06408_not_prime : ¬(recordGapCenter + 349242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349242]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06409_not_prime : ¬(recordGapCenter + 349266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349266]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06410_not_prime : ¬(recordGapCenter + 349298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349298]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06411_not_prime : ¬(recordGapCenter + 349352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349352]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06412_not_prime : ¬(recordGapCenter + 349358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349358]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06413_not_prime : ¬(recordGapCenter + 349386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349386]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06414_not_prime : ¬(recordGapCenter + 349458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349458]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06415_not_prime : ¬(recordGapCenter + 349626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349626]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06416_not_prime : ¬(recordGapCenter + 349658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349658]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06417_not_prime : ¬(recordGapCenter + 349718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349718]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06418_not_prime : ¬(recordGapCenter + 349736).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349736]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06419_not_prime : ¬(recordGapCenter + 349886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349886]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06420_not_prime : ¬(recordGapCenter + 349920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349920]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06421_not_prime : ¬(recordGapCenter + 349926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 349926]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06422_not_prime : ¬(recordGapCenter + 350000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350000]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06423_not_prime : ¬(recordGapCenter + 350072).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350072]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06424_not_prime : ¬(recordGapCenter + 350156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350156]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06425_not_prime : ¬(recordGapCenter + 350282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350282]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06426_not_prime : ¬(recordGapCenter + 350312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350312]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06427_not_prime : ¬(recordGapCenter + 350408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350408]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06428_not_prime : ¬(recordGapCenter + 350418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350418]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06429_not_prime : ¬(recordGapCenter + 350466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350466]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06430_not_prime : ¬(recordGapCenter + 350502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350502]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06431_not_prime : ¬(recordGapCenter + 350562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350562]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06432_not_prime : ¬(recordGapCenter + 350582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350582]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06433_not_prime : ¬(recordGapCenter + 350666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350666]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06434_not_prime : ¬(recordGapCenter + 350862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350862]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06435_not_prime : ¬(recordGapCenter + 350876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350876]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06436_not_prime : ¬(recordGapCenter + 350936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 350936]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06437_not_prime : ¬(recordGapCenter + 351066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351066]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06438_not_prime : ¬(recordGapCenter + 351146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351146]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06439_not_prime : ¬(recordGapCenter + 351188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351188]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06440_not_prime : ¬(recordGapCenter + 351222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351222]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06441_not_prime : ¬(recordGapCenter + 351326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351326]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06442_not_prime : ¬(recordGapCenter + 351332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351332]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06443_not_prime : ¬(recordGapCenter + 351398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351398]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06444_not_prime : ¬(recordGapCenter + 351506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351506]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06445_not_prime : ¬(recordGapCenter + 351782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351782]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06446_not_prime : ¬(recordGapCenter + 351836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351836]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06447_not_prime : ¬(recordGapCenter + 351942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 351942]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06448_not_prime : ¬(recordGapCenter + 352046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352046]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06449_not_prime : ¬(recordGapCenter + 352076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352076]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06450_not_prime : ¬(recordGapCenter + 352082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352082]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06451_not_prime : ¬(recordGapCenter + 352122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352122]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06452_not_prime : ¬(recordGapCenter + 352158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352158]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06453_not_prime : ¬(recordGapCenter + 352266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352266]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06454_not_prime : ¬(recordGapCenter + 352322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352322]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06455_not_prime : ¬(recordGapCenter + 352382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352382]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06456_not_prime : ¬(recordGapCenter + 352398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352398]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06457_not_prime : ¬(recordGapCenter + 352472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352472]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06458_not_prime : ¬(recordGapCenter + 352542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352542]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06459_not_prime : ¬(recordGapCenter + 352626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352626]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06460_not_prime : ¬(recordGapCenter + 352800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352800]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06461_not_prime : ¬(recordGapCenter + 352808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352808]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06462_not_prime : ¬(recordGapCenter + 352892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352892]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06463_not_prime : ¬(recordGapCenter + 352952).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 352952]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

theorem fullRecordGapTerm06464_not_prime : ¬(recordGapCenter + 353018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353018]
  · apply fullRecordGapRow00101_fermat
    simp [fullRecordGapRow00101_values]

end PrimeFactorUnimodality
