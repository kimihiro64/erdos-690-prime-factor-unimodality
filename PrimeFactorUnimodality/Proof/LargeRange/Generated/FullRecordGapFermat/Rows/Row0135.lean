import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00135_values : List Nat :=
  [fullRecordGapCenterValue + 511052,
    fullRecordGapCenterValue + 511142,
    fullRecordGapCenterValue + 511178,
    fullRecordGapCenterValue + 511278,
    fullRecordGapCenterValue + 511422,
    fullRecordGapCenterValue + 511458,
    fullRecordGapCenterValue + 511508,
    fullRecordGapCenterValue + 511652,
    fullRecordGapCenterValue + 511718,
    fullRecordGapCenterValue + 511838,
    fullRecordGapCenterValue + 511878,
    fullRecordGapCenterValue + 511976,
    fullRecordGapCenterValue + 512030,
    fullRecordGapCenterValue + 512166,
    fullRecordGapCenterValue + 512186,
    fullRecordGapCenterValue + 512390,
    fullRecordGapCenterValue + 512396,
    fullRecordGapCenterValue + 512438,
    fullRecordGapCenterValue + 512466,
    fullRecordGapCenterValue + 512558,
    fullRecordGapCenterValue + 512562,
    fullRecordGapCenterValue + 512570,
    fullRecordGapCenterValue + 512612,
    fullRecordGapCenterValue + 512726,
    fullRecordGapCenterValue + 512922,
    fullRecordGapCenterValue + 513122,
    fullRecordGapCenterValue + 513138,
    fullRecordGapCenterValue + 513158,
    fullRecordGapCenterValue + 513186,
    fullRecordGapCenterValue + 513290,
    fullRecordGapCenterValue + 513308,
    fullRecordGapCenterValue + 513426,
    fullRecordGapCenterValue + 513446,
    fullRecordGapCenterValue + 513626,
    fullRecordGapCenterValue + 513726,
    fullRecordGapCenterValue + 513746,
    fullRecordGapCenterValue + 513830,
    fullRecordGapCenterValue + 513908,
    fullRecordGapCenterValue + 513966,
    fullRecordGapCenterValue + 514106,
    fullRecordGapCenterValue + 514196,
    fullRecordGapCenterValue + 514218,
    fullRecordGapCenterValue + 514322,
    fullRecordGapCenterValue + 514370,
    fullRecordGapCenterValue + 514442,
    fullRecordGapCenterValue + 514500,
    fullRecordGapCenterValue + 514526,
    fullRecordGapCenterValue + 514616,
    fullRecordGapCenterValue + 514622,
    fullRecordGapCenterValue + 514652,
    fullRecordGapCenterValue + 514676,
    fullRecordGapCenterValue + 514742,
    fullRecordGapCenterValue + 514868,
    fullRecordGapCenterValue + 515022,
    fullRecordGapCenterValue + 515048,
    fullRecordGapCenterValue + 515058,
    fullRecordGapCenterValue + 515078,
    fullRecordGapCenterValue + 515118,
    fullRecordGapCenterValue + 515210,
    fullRecordGapCenterValue + 515252,
    fullRecordGapCenterValue + 515426,
    fullRecordGapCenterValue + 515492,
    fullRecordGapCenterValue + 515510,
    fullRecordGapCenterValue + 515946]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00135_fermat : ∀ n ∈ fullRecordGapRow00135_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08577_not_prime : ¬(recordGapCenter + 511052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 511052]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08578_not_prime : ¬(recordGapCenter + 511142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 511142]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08579_not_prime : ¬(recordGapCenter + 511178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 511178]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08580_not_prime : ¬(recordGapCenter + 511278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 511278]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08581_not_prime : ¬(recordGapCenter + 511422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 511422]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08582_not_prime : ¬(recordGapCenter + 511458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 511458]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08583_not_prime : ¬(recordGapCenter + 511508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 511508]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08584_not_prime : ¬(recordGapCenter + 511652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 511652]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08585_not_prime : ¬(recordGapCenter + 511718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 511718]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08586_not_prime : ¬(recordGapCenter + 511838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 511838]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08587_not_prime : ¬(recordGapCenter + 511878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 511878]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08588_not_prime : ¬(recordGapCenter + 511976).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 511976]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08589_not_prime : ¬(recordGapCenter + 512030).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512030]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08590_not_prime : ¬(recordGapCenter + 512166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512166]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08591_not_prime : ¬(recordGapCenter + 512186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512186]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08592_not_prime : ¬(recordGapCenter + 512390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512390]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08593_not_prime : ¬(recordGapCenter + 512396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512396]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08594_not_prime : ¬(recordGapCenter + 512438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512438]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08595_not_prime : ¬(recordGapCenter + 512466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512466]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08596_not_prime : ¬(recordGapCenter + 512558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512558]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08597_not_prime : ¬(recordGapCenter + 512562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512562]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08598_not_prime : ¬(recordGapCenter + 512570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512570]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08599_not_prime : ¬(recordGapCenter + 512612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512612]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08600_not_prime : ¬(recordGapCenter + 512726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512726]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08601_not_prime : ¬(recordGapCenter + 512922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 512922]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08602_not_prime : ¬(recordGapCenter + 513122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 513122]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08603_not_prime : ¬(recordGapCenter + 513138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 513138]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08604_not_prime : ¬(recordGapCenter + 513158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 513158]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08605_not_prime : ¬(recordGapCenter + 513186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 513186]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08606_not_prime : ¬(recordGapCenter + 513290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 513290]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08607_not_prime : ¬(recordGapCenter + 513308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 513308]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08608_not_prime : ¬(recordGapCenter + 513426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 513426]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08609_not_prime : ¬(recordGapCenter + 513446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 513446]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08610_not_prime : ¬(recordGapCenter + 513626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 513626]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08611_not_prime : ¬(recordGapCenter + 513726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 513726]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08612_not_prime : ¬(recordGapCenter + 513746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 513746]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08613_not_prime : ¬(recordGapCenter + 513830).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 513830]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08614_not_prime : ¬(recordGapCenter + 513908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 513908]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08615_not_prime : ¬(recordGapCenter + 513966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 513966]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08616_not_prime : ¬(recordGapCenter + 514106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 514106]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08617_not_prime : ¬(recordGapCenter + 514196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 514196]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08618_not_prime : ¬(recordGapCenter + 514218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 514218]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08619_not_prime : ¬(recordGapCenter + 514322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 514322]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08620_not_prime : ¬(recordGapCenter + 514370).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 514370]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08621_not_prime : ¬(recordGapCenter + 514442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 514442]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08622_not_prime : ¬(recordGapCenter + 514500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 514500]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08623_not_prime : ¬(recordGapCenter + 514526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 514526]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08624_not_prime : ¬(recordGapCenter + 514616).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 514616]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08625_not_prime : ¬(recordGapCenter + 514622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 514622]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08626_not_prime : ¬(recordGapCenter + 514652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 514652]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08627_not_prime : ¬(recordGapCenter + 514676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 514676]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08628_not_prime : ¬(recordGapCenter + 514742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 514742]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08629_not_prime : ¬(recordGapCenter + 514868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 514868]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08630_not_prime : ¬(recordGapCenter + 515022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 515022]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08631_not_prime : ¬(recordGapCenter + 515048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 515048]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08632_not_prime : ¬(recordGapCenter + 515058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 515058]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08633_not_prime : ¬(recordGapCenter + 515078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 515078]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08634_not_prime : ¬(recordGapCenter + 515118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 515118]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08635_not_prime : ¬(recordGapCenter + 515210).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 515210]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08636_not_prime : ¬(recordGapCenter + 515252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 515252]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08637_not_prime : ¬(recordGapCenter + 515426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 515426]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08638_not_prime : ¬(recordGapCenter + 515492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 515492]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08639_not_prime : ¬(recordGapCenter + 515510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 515510]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

theorem fullRecordGapTerm08640_not_prime : ¬(recordGapCenter + 515946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 515946]
  · apply fullRecordGapRow00135_fermat
    simp [fullRecordGapRow00135_values]

end PrimeFactorUnimodality
