import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00007_values : List Nat :=
  [fullRecordGapCenterValue - 425428,
    fullRecordGapCenterValue - 425338,
    fullRecordGapCenterValue - 425254,
    fullRecordGapCenterValue - 425250,
    fullRecordGapCenterValue - 425212,
    fullRecordGapCenterValue - 425164,
    fullRecordGapCenterValue - 425122,
    fullRecordGapCenterValue - 425094,
    fullRecordGapCenterValue - 425058,
    fullRecordGapCenterValue - 424828,
    fullRecordGapCenterValue - 424744,
    fullRecordGapCenterValue - 424738,
    fullRecordGapCenterValue - 424552,
    fullRecordGapCenterValue - 424492,
    fullRecordGapCenterValue - 424374,
    fullRecordGapCenterValue - 424282,
    fullRecordGapCenterValue - 424254,
    fullRecordGapCenterValue - 424234,
    fullRecordGapCenterValue - 424132,
    fullRecordGapCenterValue - 424114,
    fullRecordGapCenterValue - 423868,
    fullRecordGapCenterValue - 423784,
    fullRecordGapCenterValue - 423762,
    fullRecordGapCenterValue - 423622,
    fullRecordGapCenterValue - 423562,
    fullRecordGapCenterValue - 423532,
    fullRecordGapCenterValue - 423498,
    fullRecordGapCenterValue - 423454,
    fullRecordGapCenterValue - 423360,
    fullRecordGapCenterValue - 423352,
    fullRecordGapCenterValue - 423268,
    fullRecordGapCenterValue - 423222,
    fullRecordGapCenterValue - 423142,
    fullRecordGapCenterValue - 422854,
    fullRecordGapCenterValue - 422742,
    fullRecordGapCenterValue - 422574,
    fullRecordGapCenterValue - 422538,
    fullRecordGapCenterValue - 422482,
    fullRecordGapCenterValue - 422428,
    fullRecordGapCenterValue - 422398,
    fullRecordGapCenterValue - 422274,
    fullRecordGapCenterValue - 422194,
    fullRecordGapCenterValue - 422152,
    fullRecordGapCenterValue - 422068,
    fullRecordGapCenterValue - 422014,
    fullRecordGapCenterValue - 421878,
    fullRecordGapCenterValue - 421864,
    fullRecordGapCenterValue - 421738,
    fullRecordGapCenterValue - 421734,
    fullRecordGapCenterValue - 421714,
    fullRecordGapCenterValue - 421588,
    fullRecordGapCenterValue - 421522,
    fullRecordGapCenterValue - 421438,
    fullRecordGapCenterValue - 421242,
    fullRecordGapCenterValue - 421108,
    fullRecordGapCenterValue - 421054,
    fullRecordGapCenterValue - 421048,
    fullRecordGapCenterValue - 420982,
    fullRecordGapCenterValue - 420922,
    fullRecordGapCenterValue - 420874,
    fullRecordGapCenterValue - 420814,
    fullRecordGapCenterValue - 420802,
    fullRecordGapCenterValue - 420718,
    fullRecordGapCenterValue - 420664]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00007_fermat : ∀ n ∈ fullRecordGapRow00007_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00385_not_prime : ¬(recordGapCenter - 425428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425428]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00386_not_prime : ¬(recordGapCenter - 425338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425338]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00387_not_prime : ¬(recordGapCenter - 425254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425254]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00388_not_prime : ¬(recordGapCenter - 425250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425250]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00389_not_prime : ¬(recordGapCenter - 425212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425212]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00390_not_prime : ¬(recordGapCenter - 425164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425164]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00391_not_prime : ¬(recordGapCenter - 425122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425122]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00392_not_prime : ¬(recordGapCenter - 425094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425094]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00393_not_prime : ¬(recordGapCenter - 425058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 425058]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00394_not_prime : ¬(recordGapCenter - 424828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424828]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00395_not_prime : ¬(recordGapCenter - 424744).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424744]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00396_not_prime : ¬(recordGapCenter - 424738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424738]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00397_not_prime : ¬(recordGapCenter - 424552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424552]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00398_not_prime : ¬(recordGapCenter - 424492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424492]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00399_not_prime : ¬(recordGapCenter - 424374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424374]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00400_not_prime : ¬(recordGapCenter - 424282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424282]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00401_not_prime : ¬(recordGapCenter - 424254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424254]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00402_not_prime : ¬(recordGapCenter - 424234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424234]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00403_not_prime : ¬(recordGapCenter - 424132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424132]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00404_not_prime : ¬(recordGapCenter - 424114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 424114]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00405_not_prime : ¬(recordGapCenter - 423868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423868]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00406_not_prime : ¬(recordGapCenter - 423784).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423784]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00407_not_prime : ¬(recordGapCenter - 423762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423762]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00408_not_prime : ¬(recordGapCenter - 423622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423622]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00409_not_prime : ¬(recordGapCenter - 423562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423562]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00410_not_prime : ¬(recordGapCenter - 423532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423532]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00411_not_prime : ¬(recordGapCenter - 423498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423498]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00412_not_prime : ¬(recordGapCenter - 423454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423454]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00413_not_prime : ¬(recordGapCenter - 423360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423360]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00414_not_prime : ¬(recordGapCenter - 423352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423352]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00415_not_prime : ¬(recordGapCenter - 423268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423268]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00416_not_prime : ¬(recordGapCenter - 423222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423222]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00417_not_prime : ¬(recordGapCenter - 423142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 423142]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00418_not_prime : ¬(recordGapCenter - 422854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422854]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00419_not_prime : ¬(recordGapCenter - 422742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422742]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00420_not_prime : ¬(recordGapCenter - 422574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422574]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00421_not_prime : ¬(recordGapCenter - 422538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422538]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00422_not_prime : ¬(recordGapCenter - 422482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422482]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00423_not_prime : ¬(recordGapCenter - 422428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422428]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00424_not_prime : ¬(recordGapCenter - 422398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422398]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00425_not_prime : ¬(recordGapCenter - 422274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422274]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00426_not_prime : ¬(recordGapCenter - 422194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422194]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00427_not_prime : ¬(recordGapCenter - 422152).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422152]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00428_not_prime : ¬(recordGapCenter - 422068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422068]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00429_not_prime : ¬(recordGapCenter - 422014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 422014]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00430_not_prime : ¬(recordGapCenter - 421878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421878]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00431_not_prime : ¬(recordGapCenter - 421864).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421864]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00432_not_prime : ¬(recordGapCenter - 421738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421738]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00433_not_prime : ¬(recordGapCenter - 421734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421734]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00434_not_prime : ¬(recordGapCenter - 421714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421714]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00435_not_prime : ¬(recordGapCenter - 421588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421588]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00436_not_prime : ¬(recordGapCenter - 421522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421522]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00437_not_prime : ¬(recordGapCenter - 421438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421438]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00438_not_prime : ¬(recordGapCenter - 421242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421242]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00439_not_prime : ¬(recordGapCenter - 421108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421108]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00440_not_prime : ¬(recordGapCenter - 421054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421054]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00441_not_prime : ¬(recordGapCenter - 421048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 421048]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00442_not_prime : ¬(recordGapCenter - 420982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420982]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00443_not_prime : ¬(recordGapCenter - 420922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420922]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00444_not_prime : ¬(recordGapCenter - 420874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420874]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00445_not_prime : ¬(recordGapCenter - 420814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420814]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00446_not_prime : ¬(recordGapCenter - 420802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420802]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00447_not_prime : ¬(recordGapCenter - 420718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420718]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

theorem fullRecordGapTerm00448_not_prime : ¬(recordGapCenter - 420664).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420664]
  · apply fullRecordGapRow00007_fermat
    simp [fullRecordGapRow00007_values]

end PrimeFactorUnimodality
