import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00071_values : List Nat :=
  [fullRecordGapCenterValue + 156326,
    fullRecordGapCenterValue + 156458,
    fullRecordGapCenterValue + 156816,
    fullRecordGapCenterValue + 157382,
    fullRecordGapCenterValue + 157706,
    fullRecordGapCenterValue + 157778,
    fullRecordGapCenterValue + 157958,
    fullRecordGapCenterValue + 158126,
    fullRecordGapCenterValue + 158400,
    fullRecordGapCenterValue + 158466,
    fullRecordGapCenterValue + 158558,
    fullRecordGapCenterValue + 158618,
    fullRecordGapCenterValue + 158786,
    fullRecordGapCenterValue + 158798,
    fullRecordGapCenterValue + 159218,
    fullRecordGapCenterValue + 159266,
    fullRecordGapCenterValue + 159398,
    fullRecordGapCenterValue + 159602,
    fullRecordGapCenterValue + 159626,
    fullRecordGapCenterValue + 159720,
    fullRecordGapCenterValue + 159878,
    fullRecordGapCenterValue + 160142,
    fullRecordGapCenterValue + 160346,
    fullRecordGapCenterValue + 160382,
    fullRecordGapCenterValue + 160526,
    fullRecordGapCenterValue + 160682,
    fullRecordGapCenterValue + 160898,
    fullRecordGapCenterValue + 161618,
    fullRecordGapCenterValue + 161822,
    fullRecordGapCenterValue + 161858,
    fullRecordGapCenterValue + 161906,
    fullRecordGapCenterValue + 162362,
    fullRecordGapCenterValue + 162662,
    fullRecordGapCenterValue + 162878,
    fullRecordGapCenterValue + 162926,
    fullRecordGapCenterValue + 163238,
    fullRecordGapCenterValue + 163298,
    fullRecordGapCenterValue + 163350,
    fullRecordGapCenterValue + 163406,
    fullRecordGapCenterValue + 163538,
    fullRecordGapCenterValue + 163598,
    fullRecordGapCenterValue + 163706,
    fullRecordGapCenterValue + 163766,
    fullRecordGapCenterValue + 163802,
    fullRecordGapCenterValue + 163838,
    fullRecordGapCenterValue + 164018,
    fullRecordGapCenterValue + 164102,
    fullRecordGapCenterValue + 164258,
    fullRecordGapCenterValue + 164438,
    fullRecordGapCenterValue + 164678,
    fullRecordGapCenterValue + 164966,
    fullRecordGapCenterValue + 165182,
    fullRecordGapCenterValue + 165398,
    fullRecordGapCenterValue + 165518,
    fullRecordGapCenterValue + 166178,
    fullRecordGapCenterValue + 166406,
    fullRecordGapCenterValue + 166698,
    fullRecordGapCenterValue + 167126,
    fullRecordGapCenterValue + 167402,
    fullRecordGapCenterValue + 167546,
    fullRecordGapCenterValue + 167666,
    fullRecordGapCenterValue + 168326,
    fullRecordGapCenterValue + 168422,
    fullRecordGapCenterValue + 168782]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00071_fermat : ∀ n ∈ fullRecordGapRow00071_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04481_not_prime : ¬(recordGapCenter + 156326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 156326]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04482_not_prime : ¬(recordGapCenter + 156458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 156458]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04483_not_prime : ¬(recordGapCenter + 156816).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 156816]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04484_not_prime : ¬(recordGapCenter + 157382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 157382]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04485_not_prime : ¬(recordGapCenter + 157706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 157706]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04486_not_prime : ¬(recordGapCenter + 157778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 157778]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04487_not_prime : ¬(recordGapCenter + 157958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 157958]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04488_not_prime : ¬(recordGapCenter + 158126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 158126]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04489_not_prime : ¬(recordGapCenter + 158400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 158400]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04490_not_prime : ¬(recordGapCenter + 158466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 158466]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04491_not_prime : ¬(recordGapCenter + 158558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 158558]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04492_not_prime : ¬(recordGapCenter + 158618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 158618]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04493_not_prime : ¬(recordGapCenter + 158786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 158786]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04494_not_prime : ¬(recordGapCenter + 158798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 158798]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04495_not_prime : ¬(recordGapCenter + 159218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 159218]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04496_not_prime : ¬(recordGapCenter + 159266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 159266]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04497_not_prime : ¬(recordGapCenter + 159398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 159398]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04498_not_prime : ¬(recordGapCenter + 159602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 159602]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04499_not_prime : ¬(recordGapCenter + 159626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 159626]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04500_not_prime : ¬(recordGapCenter + 159720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 159720]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04501_not_prime : ¬(recordGapCenter + 159878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 159878]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04502_not_prime : ¬(recordGapCenter + 160142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 160142]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04503_not_prime : ¬(recordGapCenter + 160346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 160346]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04504_not_prime : ¬(recordGapCenter + 160382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 160382]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04505_not_prime : ¬(recordGapCenter + 160526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 160526]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04506_not_prime : ¬(recordGapCenter + 160682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 160682]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04507_not_prime : ¬(recordGapCenter + 160898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 160898]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04508_not_prime : ¬(recordGapCenter + 161618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 161618]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04509_not_prime : ¬(recordGapCenter + 161822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 161822]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04510_not_prime : ¬(recordGapCenter + 161858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 161858]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04511_not_prime : ¬(recordGapCenter + 161906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 161906]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04512_not_prime : ¬(recordGapCenter + 162362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 162362]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04513_not_prime : ¬(recordGapCenter + 162662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 162662]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04514_not_prime : ¬(recordGapCenter + 162878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 162878]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04515_not_prime : ¬(recordGapCenter + 162926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 162926]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04516_not_prime : ¬(recordGapCenter + 163238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163238]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04517_not_prime : ¬(recordGapCenter + 163298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163298]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04518_not_prime : ¬(recordGapCenter + 163350).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163350]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04519_not_prime : ¬(recordGapCenter + 163406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163406]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04520_not_prime : ¬(recordGapCenter + 163538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163538]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04521_not_prime : ¬(recordGapCenter + 163598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163598]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04522_not_prime : ¬(recordGapCenter + 163706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163706]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04523_not_prime : ¬(recordGapCenter + 163766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163766]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04524_not_prime : ¬(recordGapCenter + 163802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163802]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04525_not_prime : ¬(recordGapCenter + 163838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 163838]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04526_not_prime : ¬(recordGapCenter + 164018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 164018]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04527_not_prime : ¬(recordGapCenter + 164102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 164102]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04528_not_prime : ¬(recordGapCenter + 164258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 164258]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04529_not_prime : ¬(recordGapCenter + 164438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 164438]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04530_not_prime : ¬(recordGapCenter + 164678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 164678]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04531_not_prime : ¬(recordGapCenter + 164966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 164966]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04532_not_prime : ¬(recordGapCenter + 165182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 165182]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04533_not_prime : ¬(recordGapCenter + 165398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 165398]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04534_not_prime : ¬(recordGapCenter + 165518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 165518]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04535_not_prime : ¬(recordGapCenter + 166178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 166178]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04536_not_prime : ¬(recordGapCenter + 166406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 166406]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04537_not_prime : ¬(recordGapCenter + 166698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 166698]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04538_not_prime : ¬(recordGapCenter + 167126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 167126]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04539_not_prime : ¬(recordGapCenter + 167402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 167402]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04540_not_prime : ¬(recordGapCenter + 167546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 167546]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04541_not_prime : ¬(recordGapCenter + 167666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 167666]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04542_not_prime : ¬(recordGapCenter + 168326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 168326]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04543_not_prime : ¬(recordGapCenter + 168422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 168422]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

theorem fullRecordGapTerm04544_not_prime : ¬(recordGapCenter + 168782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 168782]
  · apply fullRecordGapRow00071_fermat
    simp [fullRecordGapRow00071_values]

end PrimeFactorUnimodality
