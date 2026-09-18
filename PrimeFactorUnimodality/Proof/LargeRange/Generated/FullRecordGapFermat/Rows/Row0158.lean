import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00158_values : List Nat :=
  [fullRecordGapCenterValue + 605508,
    fullRecordGapCenterValue + 605516,
    fullRecordGapCenterValue + 605532,
    fullRecordGapCenterValue + 605586,
    fullRecordGapCenterValue + 605732,
    fullRecordGapCenterValue + 606026,
    fullRecordGapCenterValue + 606068,
    fullRecordGapCenterValue + 606092,
    fullRecordGapCenterValue + 606098,
    fullRecordGapCenterValue + 606182,
    fullRecordGapCenterValue + 606278,
    fullRecordGapCenterValue + 606306,
    fullRecordGapCenterValue + 606468,
    fullRecordGapCenterValue + 606516,
    fullRecordGapCenterValue + 606566,
    fullRecordGapCenterValue + 606572,
    fullRecordGapCenterValue + 606642,
    fullRecordGapCenterValue + 606666,
    fullRecordGapCenterValue + 606692,
    fullRecordGapCenterValue + 606702,
    fullRecordGapCenterValue + 606926,
    fullRecordGapCenterValue + 606972,
    fullRecordGapCenterValue + 607038,
    fullRecordGapCenterValue + 607098,
    fullRecordGapCenterValue + 607142,
    fullRecordGapCenterValue + 607188,
    fullRecordGapCenterValue + 607190,
    fullRecordGapCenterValue + 607268,
    fullRecordGapCenterValue + 607358,
    fullRecordGapCenterValue + 607448,
    fullRecordGapCenterValue + 607496,
    fullRecordGapCenterValue + 607532,
    fullRecordGapCenterValue + 607686,
    fullRecordGapCenterValue + 607730,
    fullRecordGapCenterValue + 607748,
    fullRecordGapCenterValue + 607778,
    fullRecordGapCenterValue + 607862,
    fullRecordGapCenterValue + 607938,
    fullRecordGapCenterValue + 608046,
    fullRecordGapCenterValue + 608108,
    fullRecordGapCenterValue + 608126,
    fullRecordGapCenterValue + 608162,
    fullRecordGapCenterValue + 608298,
    fullRecordGapCenterValue + 608466,
    fullRecordGapCenterValue + 608606,
    fullRecordGapCenterValue + 608676,
    fullRecordGapCenterValue + 608732,
    fullRecordGapCenterValue + 608756,
    fullRecordGapCenterValue + 608858,
    fullRecordGapCenterValue + 608876,
    fullRecordGapCenterValue + 608898,
    fullRecordGapCenterValue + 608918,
    fullRecordGapCenterValue + 609036,
    fullRecordGapCenterValue + 609078,
    fullRecordGapCenterValue + 609170,
    fullRecordGapCenterValue + 609186,
    fullRecordGapCenterValue + 609276,
    fullRecordGapCenterValue + 609302,
    fullRecordGapCenterValue + 609326,
    fullRecordGapCenterValue + 609366,
    fullRecordGapCenterValue + 609438,
    fullRecordGapCenterValue + 609458,
    fullRecordGapCenterValue + 609486,
    fullRecordGapCenterValue + 609578]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00158_fermat : ∀ n ∈ fullRecordGapRow00158_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10049_not_prime : ¬(recordGapCenter + 605508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 605508]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10050_not_prime : ¬(recordGapCenter + 605516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 605516]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10051_not_prime : ¬(recordGapCenter + 605532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 605532]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10052_not_prime : ¬(recordGapCenter + 605586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 605586]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10053_not_prime : ¬(recordGapCenter + 605732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 605732]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10054_not_prime : ¬(recordGapCenter + 606026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606026]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10055_not_prime : ¬(recordGapCenter + 606068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606068]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10056_not_prime : ¬(recordGapCenter + 606092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606092]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10057_not_prime : ¬(recordGapCenter + 606098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606098]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10058_not_prime : ¬(recordGapCenter + 606182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606182]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10059_not_prime : ¬(recordGapCenter + 606278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606278]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10060_not_prime : ¬(recordGapCenter + 606306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606306]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10061_not_prime : ¬(recordGapCenter + 606468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606468]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10062_not_prime : ¬(recordGapCenter + 606516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606516]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10063_not_prime : ¬(recordGapCenter + 606566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606566]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10064_not_prime : ¬(recordGapCenter + 606572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606572]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10065_not_prime : ¬(recordGapCenter + 606642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606642]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10066_not_prime : ¬(recordGapCenter + 606666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606666]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10067_not_prime : ¬(recordGapCenter + 606692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606692]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10068_not_prime : ¬(recordGapCenter + 606702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606702]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10069_not_prime : ¬(recordGapCenter + 606926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606926]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10070_not_prime : ¬(recordGapCenter + 606972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 606972]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10071_not_prime : ¬(recordGapCenter + 607038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607038]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10072_not_prime : ¬(recordGapCenter + 607098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607098]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10073_not_prime : ¬(recordGapCenter + 607142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607142]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10074_not_prime : ¬(recordGapCenter + 607188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607188]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10075_not_prime : ¬(recordGapCenter + 607190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607190]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10076_not_prime : ¬(recordGapCenter + 607268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607268]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10077_not_prime : ¬(recordGapCenter + 607358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607358]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10078_not_prime : ¬(recordGapCenter + 607448).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607448]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10079_not_prime : ¬(recordGapCenter + 607496).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607496]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10080_not_prime : ¬(recordGapCenter + 607532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607532]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10081_not_prime : ¬(recordGapCenter + 607686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607686]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10082_not_prime : ¬(recordGapCenter + 607730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607730]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10083_not_prime : ¬(recordGapCenter + 607748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607748]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10084_not_prime : ¬(recordGapCenter + 607778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607778]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10085_not_prime : ¬(recordGapCenter + 607862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607862]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10086_not_prime : ¬(recordGapCenter + 607938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 607938]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10087_not_prime : ¬(recordGapCenter + 608046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 608046]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10088_not_prime : ¬(recordGapCenter + 608108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 608108]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10089_not_prime : ¬(recordGapCenter + 608126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 608126]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10090_not_prime : ¬(recordGapCenter + 608162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 608162]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10091_not_prime : ¬(recordGapCenter + 608298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 608298]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10092_not_prime : ¬(recordGapCenter + 608466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 608466]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10093_not_prime : ¬(recordGapCenter + 608606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 608606]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10094_not_prime : ¬(recordGapCenter + 608676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 608676]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10095_not_prime : ¬(recordGapCenter + 608732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 608732]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10096_not_prime : ¬(recordGapCenter + 608756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 608756]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10097_not_prime : ¬(recordGapCenter + 608858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 608858]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10098_not_prime : ¬(recordGapCenter + 608876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 608876]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10099_not_prime : ¬(recordGapCenter + 608898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 608898]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10100_not_prime : ¬(recordGapCenter + 608918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 608918]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10101_not_prime : ¬(recordGapCenter + 609036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609036]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10102_not_prime : ¬(recordGapCenter + 609078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609078]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10103_not_prime : ¬(recordGapCenter + 609170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609170]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10104_not_prime : ¬(recordGapCenter + 609186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609186]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10105_not_prime : ¬(recordGapCenter + 609276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609276]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10106_not_prime : ¬(recordGapCenter + 609302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609302]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10107_not_prime : ¬(recordGapCenter + 609326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609326]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10108_not_prime : ¬(recordGapCenter + 609366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609366]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10109_not_prime : ¬(recordGapCenter + 609438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609438]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10110_not_prime : ¬(recordGapCenter + 609458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609458]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10111_not_prime : ¬(recordGapCenter + 609486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609486]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

theorem fullRecordGapTerm10112_not_prime : ¬(recordGapCenter + 609578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 609578]
  · apply fullRecordGapRow00158_fermat
    simp [fullRecordGapRow00158_values]

end PrimeFactorUnimodality
