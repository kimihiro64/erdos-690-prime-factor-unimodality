import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00037_values : List Nat :=
  [fullRecordGapCenterValue - 264742,
    fullRecordGapCenterValue - 264714,
    fullRecordGapCenterValue - 264600,
    fullRecordGapCenterValue - 264514,
    fullRecordGapCenterValue - 264274,
    fullRecordGapCenterValue - 264162,
    fullRecordGapCenterValue - 264148,
    fullRecordGapCenterValue - 264142,
    fullRecordGapCenterValue - 264102,
    fullRecordGapCenterValue - 263932,
    fullRecordGapCenterValue - 263878,
    fullRecordGapCenterValue - 263854,
    fullRecordGapCenterValue - 263814,
    fullRecordGapCenterValue - 263778,
    fullRecordGapCenterValue - 263598,
    fullRecordGapCenterValue - 263554,
    fullRecordGapCenterValue - 263518,
    fullRecordGapCenterValue - 263422,
    fullRecordGapCenterValue - 263202,
    fullRecordGapCenterValue - 263182,
    fullRecordGapCenterValue - 263118,
    fullRecordGapCenterValue - 263044,
    fullRecordGapCenterValue - 262978,
    fullRecordGapCenterValue - 262954,
    fullRecordGapCenterValue - 262894,
    fullRecordGapCenterValue - 262852,
    fullRecordGapCenterValue - 262762,
    fullRecordGapCenterValue - 262722,
    fullRecordGapCenterValue - 262714,
    fullRecordGapCenterValue - 262698,
    fullRecordGapCenterValue - 262642,
    fullRecordGapCenterValue - 262594,
    fullRecordGapCenterValue - 262554,
    fullRecordGapCenterValue - 262498,
    fullRecordGapCenterValue - 262440,
    fullRecordGapCenterValue - 262348,
    fullRecordGapCenterValue - 262324,
    fullRecordGapCenterValue - 262258,
    fullRecordGapCenterValue - 262204,
    fullRecordGapCenterValue - 262084,
    fullRecordGapCenterValue - 262014,
    fullRecordGapCenterValue - 261954,
    fullRecordGapCenterValue - 261798,
    fullRecordGapCenterValue - 261762,
    fullRecordGapCenterValue - 261748,
    fullRecordGapCenterValue - 261634,
    fullRecordGapCenterValue - 261622,
    fullRecordGapCenterValue - 261582,
    fullRecordGapCenterValue - 261574,
    fullRecordGapCenterValue - 261462,
    fullRecordGapCenterValue - 261412,
    fullRecordGapCenterValue - 261292,
    fullRecordGapCenterValue - 261238,
    fullRecordGapCenterValue - 261028,
    fullRecordGapCenterValue - 260922,
    fullRecordGapCenterValue - 260878,
    fullRecordGapCenterValue - 260818,
    fullRecordGapCenterValue - 260812,
    fullRecordGapCenterValue - 260742,
    fullRecordGapCenterValue - 260614,
    fullRecordGapCenterValue - 260518,
    fullRecordGapCenterValue - 260404,
    fullRecordGapCenterValue - 260398,
    fullRecordGapCenterValue - 260382]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00037_fermat : ∀ n ∈ fullRecordGapRow00037_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02305_not_prime : ¬(recordGapCenter - 264742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264742]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02306_not_prime : ¬(recordGapCenter - 264714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264714]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02307_not_prime : ¬(recordGapCenter - 264600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264600]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02308_not_prime : ¬(recordGapCenter - 264514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264514]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02309_not_prime : ¬(recordGapCenter - 264274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264274]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02310_not_prime : ¬(recordGapCenter - 264162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264162]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02311_not_prime : ¬(recordGapCenter - 264148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264148]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02312_not_prime : ¬(recordGapCenter - 264142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264142]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02313_not_prime : ¬(recordGapCenter - 264102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264102]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02314_not_prime : ¬(recordGapCenter - 263932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263932]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02315_not_prime : ¬(recordGapCenter - 263878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263878]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02316_not_prime : ¬(recordGapCenter - 263854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263854]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02317_not_prime : ¬(recordGapCenter - 263814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263814]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02318_not_prime : ¬(recordGapCenter - 263778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263778]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02319_not_prime : ¬(recordGapCenter - 263598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263598]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02320_not_prime : ¬(recordGapCenter - 263554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263554]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02321_not_prime : ¬(recordGapCenter - 263518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263518]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02322_not_prime : ¬(recordGapCenter - 263422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263422]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02323_not_prime : ¬(recordGapCenter - 263202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263202]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02324_not_prime : ¬(recordGapCenter - 263182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263182]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02325_not_prime : ¬(recordGapCenter - 263118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263118]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02326_not_prime : ¬(recordGapCenter - 263044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263044]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02327_not_prime : ¬(recordGapCenter - 262978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262978]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02328_not_prime : ¬(recordGapCenter - 262954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262954]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02329_not_prime : ¬(recordGapCenter - 262894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262894]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02330_not_prime : ¬(recordGapCenter - 262852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262852]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02331_not_prime : ¬(recordGapCenter - 262762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262762]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02332_not_prime : ¬(recordGapCenter - 262722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262722]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02333_not_prime : ¬(recordGapCenter - 262714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262714]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02334_not_prime : ¬(recordGapCenter - 262698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262698]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02335_not_prime : ¬(recordGapCenter - 262642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262642]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02336_not_prime : ¬(recordGapCenter - 262594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262594]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02337_not_prime : ¬(recordGapCenter - 262554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262554]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02338_not_prime : ¬(recordGapCenter - 262498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262498]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02339_not_prime : ¬(recordGapCenter - 262440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262440]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02340_not_prime : ¬(recordGapCenter - 262348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262348]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02341_not_prime : ¬(recordGapCenter - 262324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262324]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02342_not_prime : ¬(recordGapCenter - 262258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262258]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02343_not_prime : ¬(recordGapCenter - 262204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262204]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02344_not_prime : ¬(recordGapCenter - 262084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262084]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02345_not_prime : ¬(recordGapCenter - 262014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262014]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02346_not_prime : ¬(recordGapCenter - 261954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261954]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02347_not_prime : ¬(recordGapCenter - 261798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261798]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02348_not_prime : ¬(recordGapCenter - 261762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261762]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02349_not_prime : ¬(recordGapCenter - 261748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261748]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02350_not_prime : ¬(recordGapCenter - 261634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261634]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02351_not_prime : ¬(recordGapCenter - 261622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261622]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02352_not_prime : ¬(recordGapCenter - 261582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261582]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02353_not_prime : ¬(recordGapCenter - 261574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261574]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02354_not_prime : ¬(recordGapCenter - 261462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261462]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02355_not_prime : ¬(recordGapCenter - 261412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261412]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02356_not_prime : ¬(recordGapCenter - 261292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261292]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02357_not_prime : ¬(recordGapCenter - 261238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261238]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02358_not_prime : ¬(recordGapCenter - 261028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261028]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02359_not_prime : ¬(recordGapCenter - 260922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260922]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02360_not_prime : ¬(recordGapCenter - 260878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260878]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02361_not_prime : ¬(recordGapCenter - 260818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260818]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02362_not_prime : ¬(recordGapCenter - 260812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260812]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02363_not_prime : ¬(recordGapCenter - 260742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260742]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02364_not_prime : ¬(recordGapCenter - 260614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260614]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02365_not_prime : ¬(recordGapCenter - 260518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260518]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02366_not_prime : ¬(recordGapCenter - 260404).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260404]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02367_not_prime : ¬(recordGapCenter - 260398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260398]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

theorem fullRecordGapTerm02368_not_prime : ¬(recordGapCenter - 260382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260382]
  · apply fullRecordGapRow00037_fermat
    simp [fullRecordGapRow00037_values]

end PrimeFactorUnimodality
