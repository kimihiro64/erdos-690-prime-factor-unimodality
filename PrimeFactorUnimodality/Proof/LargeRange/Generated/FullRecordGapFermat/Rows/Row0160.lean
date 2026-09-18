import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00160_values : List Nat :=
  [fullRecordGapCenterValue + 613208,
    fullRecordGapCenterValue + 613308,
    fullRecordGapCenterValue + 613406,
    fullRecordGapCenterValue + 613506,
    fullRecordGapCenterValue + 613518,
    fullRecordGapCenterValue + 613562,
    fullRecordGapCenterValue + 613572,
    fullRecordGapCenterValue + 613596,
    fullRecordGapCenterValue + 613628,
    fullRecordGapCenterValue + 613758,
    fullRecordGapCenterValue + 613790,
    fullRecordGapCenterValue + 613806,
    fullRecordGapCenterValue + 613902,
    fullRecordGapCenterValue + 614030,
    fullRecordGapCenterValue + 614132,
    fullRecordGapCenterValue + 614168,
    fullRecordGapCenterValue + 614342,
    fullRecordGapCenterValue + 614378,
    fullRecordGapCenterValue + 614408,
    fullRecordGapCenterValue + 614436,
    fullRecordGapCenterValue + 614486,
    fullRecordGapCenterValue + 614546,
    fullRecordGapCenterValue + 614552,
    fullRecordGapCenterValue + 614598,
    fullRecordGapCenterValue + 614630,
    fullRecordGapCenterValue + 614678,
    fullRecordGapCenterValue + 614696,
    fullRecordGapCenterValue + 614706,
    fullRecordGapCenterValue + 614748,
    fullRecordGapCenterValue + 614756,
    fullRecordGapCenterValue + 614868,
    fullRecordGapCenterValue + 614892,
    fullRecordGapCenterValue + 614922,
    fullRecordGapCenterValue + 614930,
    fullRecordGapCenterValue + 614982,
    fullRecordGapCenterValue + 615198,
    fullRecordGapCenterValue + 615282,
    fullRecordGapCenterValue + 615386,
    fullRecordGapCenterValue + 615566,
    fullRecordGapCenterValue + 615590,
    fullRecordGapCenterValue + 615746,
    fullRecordGapCenterValue + 615788,
    fullRecordGapCenterValue + 615830,
    fullRecordGapCenterValue + 615878,
    fullRecordGapCenterValue + 615918,
    fullRecordGapCenterValue + 615938,
    fullRecordGapCenterValue + 616038,
    fullRecordGapCenterValue + 616082,
    fullRecordGapCenterValue + 616092,
    fullRecordGapCenterValue + 616136,
    fullRecordGapCenterValue + 616292,
    fullRecordGapCenterValue + 616298,
    fullRecordGapCenterValue + 616316,
    fullRecordGapCenterValue + 616406,
    fullRecordGapCenterValue + 616526,
    fullRecordGapCenterValue + 616578,
    fullRecordGapCenterValue + 616596,
    fullRecordGapCenterValue + 616628,
    fullRecordGapCenterValue + 616718,
    fullRecordGapCenterValue + 616782,
    fullRecordGapCenterValue + 616866,
    fullRecordGapCenterValue + 617018,
    fullRecordGapCenterValue + 617046,
    fullRecordGapCenterValue + 617102]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00160_fermat : ∀ n ∈ fullRecordGapRow00160_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10177_not_prime : ¬(recordGapCenter + 613208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613208]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10178_not_prime : ¬(recordGapCenter + 613308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613308]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10179_not_prime : ¬(recordGapCenter + 613406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613406]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10180_not_prime : ¬(recordGapCenter + 613506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613506]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10181_not_prime : ¬(recordGapCenter + 613518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613518]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10182_not_prime : ¬(recordGapCenter + 613562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613562]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10183_not_prime : ¬(recordGapCenter + 613572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613572]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10184_not_prime : ¬(recordGapCenter + 613596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613596]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10185_not_prime : ¬(recordGapCenter + 613628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613628]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10186_not_prime : ¬(recordGapCenter + 613758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613758]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10187_not_prime : ¬(recordGapCenter + 613790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613790]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10188_not_prime : ¬(recordGapCenter + 613806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613806]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10189_not_prime : ¬(recordGapCenter + 613902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 613902]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10190_not_prime : ¬(recordGapCenter + 614030).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614030]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10191_not_prime : ¬(recordGapCenter + 614132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614132]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10192_not_prime : ¬(recordGapCenter + 614168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614168]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10193_not_prime : ¬(recordGapCenter + 614342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614342]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10194_not_prime : ¬(recordGapCenter + 614378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614378]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10195_not_prime : ¬(recordGapCenter + 614408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614408]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10196_not_prime : ¬(recordGapCenter + 614436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614436]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10197_not_prime : ¬(recordGapCenter + 614486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614486]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10198_not_prime : ¬(recordGapCenter + 614546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614546]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10199_not_prime : ¬(recordGapCenter + 614552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614552]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10200_not_prime : ¬(recordGapCenter + 614598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614598]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10201_not_prime : ¬(recordGapCenter + 614630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614630]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10202_not_prime : ¬(recordGapCenter + 614678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614678]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10203_not_prime : ¬(recordGapCenter + 614696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614696]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10204_not_prime : ¬(recordGapCenter + 614706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614706]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10205_not_prime : ¬(recordGapCenter + 614748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614748]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10206_not_prime : ¬(recordGapCenter + 614756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614756]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10207_not_prime : ¬(recordGapCenter + 614868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614868]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10208_not_prime : ¬(recordGapCenter + 614892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614892]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10209_not_prime : ¬(recordGapCenter + 614922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614922]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10210_not_prime : ¬(recordGapCenter + 614930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614930]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10211_not_prime : ¬(recordGapCenter + 614982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 614982]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10212_not_prime : ¬(recordGapCenter + 615198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 615198]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10213_not_prime : ¬(recordGapCenter + 615282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 615282]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10214_not_prime : ¬(recordGapCenter + 615386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 615386]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10215_not_prime : ¬(recordGapCenter + 615566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 615566]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10216_not_prime : ¬(recordGapCenter + 615590).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 615590]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10217_not_prime : ¬(recordGapCenter + 615746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 615746]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10218_not_prime : ¬(recordGapCenter + 615788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 615788]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10219_not_prime : ¬(recordGapCenter + 615830).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 615830]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10220_not_prime : ¬(recordGapCenter + 615878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 615878]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10221_not_prime : ¬(recordGapCenter + 615918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 615918]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10222_not_prime : ¬(recordGapCenter + 615938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 615938]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10223_not_prime : ¬(recordGapCenter + 616038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616038]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10224_not_prime : ¬(recordGapCenter + 616082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616082]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10225_not_prime : ¬(recordGapCenter + 616092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616092]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10226_not_prime : ¬(recordGapCenter + 616136).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616136]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10227_not_prime : ¬(recordGapCenter + 616292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616292]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10228_not_prime : ¬(recordGapCenter + 616298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616298]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10229_not_prime : ¬(recordGapCenter + 616316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616316]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10230_not_prime : ¬(recordGapCenter + 616406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616406]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10231_not_prime : ¬(recordGapCenter + 616526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616526]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10232_not_prime : ¬(recordGapCenter + 616578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616578]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10233_not_prime : ¬(recordGapCenter + 616596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616596]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10234_not_prime : ¬(recordGapCenter + 616628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616628]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10235_not_prime : ¬(recordGapCenter + 616718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616718]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10236_not_prime : ¬(recordGapCenter + 616782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616782]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10237_not_prime : ¬(recordGapCenter + 616866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 616866]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10238_not_prime : ¬(recordGapCenter + 617018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617018]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10239_not_prime : ¬(recordGapCenter + 617046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617046]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

theorem fullRecordGapTerm10240_not_prime : ¬(recordGapCenter + 617102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 617102]
  · apply fullRecordGapRow00160_fermat
    simp [fullRecordGapRow00160_values]

end PrimeFactorUnimodality
