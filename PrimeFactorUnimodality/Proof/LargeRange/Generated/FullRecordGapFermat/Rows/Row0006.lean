import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00006_values : List Nat :=
  [fullRecordGapCenterValue - 430842,
    fullRecordGapCenterValue - 430834,
    fullRecordGapCenterValue - 430792,
    fullRecordGapCenterValue - 430762,
    fullRecordGapCenterValue - 430734,
    fullRecordGapCenterValue - 430684,
    fullRecordGapCenterValue - 430594,
    fullRecordGapCenterValue - 430558,
    fullRecordGapCenterValue - 430552,
    fullRecordGapCenterValue - 430264,
    fullRecordGapCenterValue - 430174,
    fullRecordGapCenterValue - 430072,
    fullRecordGapCenterValue - 429798,
    fullRecordGapCenterValue - 429622,
    fullRecordGapCenterValue - 429544,
    fullRecordGapCenterValue - 429508,
    fullRecordGapCenterValue - 429414,
    fullRecordGapCenterValue - 429222,
    fullRecordGapCenterValue - 429064,
    fullRecordGapCenterValue - 428998,
    fullRecordGapCenterValue - 428878,
    fullRecordGapCenterValue - 428788,
    fullRecordGapCenterValue - 428782,
    fullRecordGapCenterValue - 428728,
    fullRecordGapCenterValue - 428658,
    fullRecordGapCenterValue - 428622,
    fullRecordGapCenterValue - 428334,
    fullRecordGapCenterValue - 427998,
    fullRecordGapCenterValue - 427972,
    fullRecordGapCenterValue - 427962,
    fullRecordGapCenterValue - 427902,
    fullRecordGapCenterValue - 427894,
    fullRecordGapCenterValue - 427858,
    fullRecordGapCenterValue - 427852,
    fullRecordGapCenterValue - 427828,
    fullRecordGapCenterValue - 427762,
    fullRecordGapCenterValue - 427528,
    fullRecordGapCenterValue - 427474,
    fullRecordGapCenterValue - 427468,
    fullRecordGapCenterValue - 427444,
    fullRecordGapCenterValue - 427282,
    fullRecordGapCenterValue - 427254,
    fullRecordGapCenterValue - 427012,
    fullRecordGapCenterValue - 426982,
    fullRecordGapCenterValue - 426934,
    fullRecordGapCenterValue - 426898,
    fullRecordGapCenterValue - 426888,
    fullRecordGapCenterValue - 426772,
    fullRecordGapCenterValue - 426724,
    fullRecordGapCenterValue - 426534,
    fullRecordGapCenterValue - 426508,
    fullRecordGapCenterValue - 426484,
    fullRecordGapCenterValue - 426418,
    fullRecordGapCenterValue - 426414,
    fullRecordGapCenterValue - 426354,
    fullRecordGapCenterValue - 426138,
    fullRecordGapCenterValue - 426124,
    fullRecordGapCenterValue - 426004,
    fullRecordGapCenterValue - 425994,
    fullRecordGapCenterValue - 425974,
    fullRecordGapCenterValue - 425962,
    fullRecordGapCenterValue - 425848,
    fullRecordGapCenterValue - 425694,
    fullRecordGapCenterValue - 425512]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00006_fermat : ∀ n ∈ fullRecordGapRow00006_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00321_not_prime : ¬(recordGapCenter - 430842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430842]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00322_not_prime : ¬(recordGapCenter - 430834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430834]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00323_not_prime : ¬(recordGapCenter - 430792).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430792]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00324_not_prime : ¬(recordGapCenter - 430762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430762]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00325_not_prime : ¬(recordGapCenter - 430734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430734]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00326_not_prime : ¬(recordGapCenter - 430684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430684]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00327_not_prime : ¬(recordGapCenter - 430594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430594]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00328_not_prime : ¬(recordGapCenter - 430558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430558]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00329_not_prime : ¬(recordGapCenter - 430552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430552]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00330_not_prime : ¬(recordGapCenter - 430264).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430264]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00331_not_prime : ¬(recordGapCenter - 430174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430174]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00332_not_prime : ¬(recordGapCenter - 430072).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430072]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00333_not_prime : ¬(recordGapCenter - 429798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 429798]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00334_not_prime : ¬(recordGapCenter - 429622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 429622]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00335_not_prime : ¬(recordGapCenter - 429544).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 429544]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00336_not_prime : ¬(recordGapCenter - 429508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 429508]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00337_not_prime : ¬(recordGapCenter - 429414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 429414]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00338_not_prime : ¬(recordGapCenter - 429222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 429222]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00339_not_prime : ¬(recordGapCenter - 429064).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 429064]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00340_not_prime : ¬(recordGapCenter - 428998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428998]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00341_not_prime : ¬(recordGapCenter - 428878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428878]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00342_not_prime : ¬(recordGapCenter - 428788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428788]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00343_not_prime : ¬(recordGapCenter - 428782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428782]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00344_not_prime : ¬(recordGapCenter - 428728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428728]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00345_not_prime : ¬(recordGapCenter - 428658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428658]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00346_not_prime : ¬(recordGapCenter - 428622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428622]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00347_not_prime : ¬(recordGapCenter - 428334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 428334]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00348_not_prime : ¬(recordGapCenter - 427998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427998]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00349_not_prime : ¬(recordGapCenter - 427972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427972]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00350_not_prime : ¬(recordGapCenter - 427962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427962]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00351_not_prime : ¬(recordGapCenter - 427902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427902]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00352_not_prime : ¬(recordGapCenter - 427894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427894]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00353_not_prime : ¬(recordGapCenter - 427858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427858]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00354_not_prime : ¬(recordGapCenter - 427852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427852]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00355_not_prime : ¬(recordGapCenter - 427828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427828]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00356_not_prime : ¬(recordGapCenter - 427762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427762]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00357_not_prime : ¬(recordGapCenter - 427528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427528]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00358_not_prime : ¬(recordGapCenter - 427474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427474]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00359_not_prime : ¬(recordGapCenter - 427468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427468]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00360_not_prime : ¬(recordGapCenter - 427444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427444]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00361_not_prime : ¬(recordGapCenter - 427282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427282]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00362_not_prime : ¬(recordGapCenter - 427254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427254]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00363_not_prime : ¬(recordGapCenter - 427012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 427012]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00364_not_prime : ¬(recordGapCenter - 426982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426982]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00365_not_prime : ¬(recordGapCenter - 426934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426934]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00366_not_prime : ¬(recordGapCenter - 426898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426898]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00367_not_prime : ¬(recordGapCenter - 426888).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426888]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00368_not_prime : ¬(recordGapCenter - 426772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426772]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00369_not_prime : ¬(recordGapCenter - 426724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426724]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00370_not_prime : ¬(recordGapCenter - 426534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426534]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00371_not_prime : ¬(recordGapCenter - 426508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426508]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00372_not_prime : ¬(recordGapCenter - 426484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426484]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00373_not_prime : ¬(recordGapCenter - 426418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426418]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00374_not_prime : ¬(recordGapCenter - 426414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426414]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00375_not_prime : ¬(recordGapCenter - 426354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426354]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00376_not_prime : ¬(recordGapCenter - 426138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426138]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00377_not_prime : ¬(recordGapCenter - 426124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426124]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00378_not_prime : ¬(recordGapCenter - 426004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 426004]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00379_not_prime : ¬(recordGapCenter - 425994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425994]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00380_not_prime : ¬(recordGapCenter - 425974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425974]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00381_not_prime : ¬(recordGapCenter - 425962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425962]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00382_not_prime : ¬(recordGapCenter - 425848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425848]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00383_not_prime : ¬(recordGapCenter - 425694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425694]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

theorem fullRecordGapTerm00384_not_prime : ¬(recordGapCenter - 425512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425512]
  · apply fullRecordGapRow00006_fermat
    simp [fullRecordGapRow00006_values]

end PrimeFactorUnimodality
