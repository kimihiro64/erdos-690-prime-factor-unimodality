import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00042_values : List Nat :=
  [fullRecordGapCenterValue - 227692,
    fullRecordGapCenterValue - 227674,
    fullRecordGapCenterValue - 227434,
    fullRecordGapCenterValue - 227428,
    fullRecordGapCenterValue - 227182,
    fullRecordGapCenterValue - 227134,
    fullRecordGapCenterValue - 227092,
    fullRecordGapCenterValue - 227068,
    fullRecordGapCenterValue - 227002,
    fullRecordGapCenterValue - 226558,
    fullRecordGapCenterValue - 226294,
    fullRecordGapCenterValue - 226222,
    fullRecordGapCenterValue - 226162,
    fullRecordGapCenterValue - 226102,
    fullRecordGapCenterValue - 226078,
    fullRecordGapCenterValue - 226042,
    fullRecordGapCenterValue - 226012,
    fullRecordGapCenterValue - 225994,
    fullRecordGapCenterValue - 225868,
    fullRecordGapCenterValue - 225748,
    fullRecordGapCenterValue - 225718,
    fullRecordGapCenterValue - 225598,
    fullRecordGapCenterValue - 225532,
    fullRecordGapCenterValue - 225514,
    fullRecordGapCenterValue - 225154,
    fullRecordGapCenterValue - 225118,
    fullRecordGapCenterValue - 225000,
    fullRecordGapCenterValue - 224788,
    fullRecordGapCenterValue - 224674,
    fullRecordGapCenterValue - 224662,
    fullRecordGapCenterValue - 224524,
    fullRecordGapCenterValue - 224494,
    fullRecordGapCenterValue - 224398,
    fullRecordGapCenterValue - 224362,
    fullRecordGapCenterValue - 224278,
    fullRecordGapCenterValue - 224212,
    fullRecordGapCenterValue - 224194,
    fullRecordGapCenterValue - 224164,
    fullRecordGapCenterValue - 224038,
    fullRecordGapCenterValue - 223918,
    fullRecordGapCenterValue - 223732,
    fullRecordGapCenterValue - 223654,
    fullRecordGapCenterValue - 223582,
    fullRecordGapCenterValue - 223318,
    fullRecordGapCenterValue - 223228,
    fullRecordGapCenterValue - 223078,
    fullRecordGapCenterValue - 222934,
    fullRecordGapCenterValue - 222862,
    fullRecordGapCenterValue - 222694,
    fullRecordGapCenterValue - 222652,
    fullRecordGapCenterValue - 222532,
    fullRecordGapCenterValue - 222484,
    fullRecordGapCenterValue - 222238,
    fullRecordGapCenterValue - 222058,
    fullRecordGapCenterValue - 222004,
    fullRecordGapCenterValue - 221902,
    fullRecordGapCenterValue - 221842,
    fullRecordGapCenterValue - 221758,
    fullRecordGapCenterValue - 221644,
    fullRecordGapCenterValue - 221458,
    fullRecordGapCenterValue - 221332,
    fullRecordGapCenterValue - 221218,
    fullRecordGapCenterValue - 221164,
    fullRecordGapCenterValue - 220882]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00042_fermat : ∀ n ∈ fullRecordGapRow00042_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02625_not_prime : ¬(recordGapCenter - 227692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227692]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02626_not_prime : ¬(recordGapCenter - 227674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227674]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02627_not_prime : ¬(recordGapCenter - 227434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227434]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02628_not_prime : ¬(recordGapCenter - 227428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227428]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02629_not_prime : ¬(recordGapCenter - 227182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227182]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02630_not_prime : ¬(recordGapCenter - 227134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227134]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02631_not_prime : ¬(recordGapCenter - 227092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227092]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02632_not_prime : ¬(recordGapCenter - 227068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227068]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02633_not_prime : ¬(recordGapCenter - 227002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227002]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02634_not_prime : ¬(recordGapCenter - 226558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226558]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02635_not_prime : ¬(recordGapCenter - 226294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226294]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02636_not_prime : ¬(recordGapCenter - 226222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226222]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02637_not_prime : ¬(recordGapCenter - 226162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226162]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02638_not_prime : ¬(recordGapCenter - 226102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226102]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02639_not_prime : ¬(recordGapCenter - 226078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226078]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02640_not_prime : ¬(recordGapCenter - 226042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226042]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02641_not_prime : ¬(recordGapCenter - 226012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226012]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02642_not_prime : ¬(recordGapCenter - 225994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225994]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02643_not_prime : ¬(recordGapCenter - 225868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225868]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02644_not_prime : ¬(recordGapCenter - 225748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225748]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02645_not_prime : ¬(recordGapCenter - 225718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225718]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02646_not_prime : ¬(recordGapCenter - 225598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225598]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02647_not_prime : ¬(recordGapCenter - 225532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225532]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02648_not_prime : ¬(recordGapCenter - 225514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225514]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02649_not_prime : ¬(recordGapCenter - 225154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225154]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02650_not_prime : ¬(recordGapCenter - 225118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225118]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02651_not_prime : ¬(recordGapCenter - 225000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225000]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02652_not_prime : ¬(recordGapCenter - 224788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224788]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02653_not_prime : ¬(recordGapCenter - 224674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224674]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02654_not_prime : ¬(recordGapCenter - 224662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224662]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02655_not_prime : ¬(recordGapCenter - 224524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224524]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02656_not_prime : ¬(recordGapCenter - 224494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224494]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02657_not_prime : ¬(recordGapCenter - 224398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224398]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02658_not_prime : ¬(recordGapCenter - 224362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224362]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02659_not_prime : ¬(recordGapCenter - 224278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224278]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02660_not_prime : ¬(recordGapCenter - 224212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224212]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02661_not_prime : ¬(recordGapCenter - 224194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224194]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02662_not_prime : ¬(recordGapCenter - 224164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224164]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02663_not_prime : ¬(recordGapCenter - 224038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224038]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02664_not_prime : ¬(recordGapCenter - 223918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 223918]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02665_not_prime : ¬(recordGapCenter - 223732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 223732]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02666_not_prime : ¬(recordGapCenter - 223654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 223654]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02667_not_prime : ¬(recordGapCenter - 223582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 223582]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02668_not_prime : ¬(recordGapCenter - 223318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 223318]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02669_not_prime : ¬(recordGapCenter - 223228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 223228]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02670_not_prime : ¬(recordGapCenter - 223078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 223078]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02671_not_prime : ¬(recordGapCenter - 222934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222934]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02672_not_prime : ¬(recordGapCenter - 222862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222862]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02673_not_prime : ¬(recordGapCenter - 222694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222694]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02674_not_prime : ¬(recordGapCenter - 222652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222652]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02675_not_prime : ¬(recordGapCenter - 222532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222532]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02676_not_prime : ¬(recordGapCenter - 222484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222484]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02677_not_prime : ¬(recordGapCenter - 222238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222238]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02678_not_prime : ¬(recordGapCenter - 222058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222058]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02679_not_prime : ¬(recordGapCenter - 222004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222004]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02680_not_prime : ¬(recordGapCenter - 221902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221902]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02681_not_prime : ¬(recordGapCenter - 221842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221842]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02682_not_prime : ¬(recordGapCenter - 221758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221758]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02683_not_prime : ¬(recordGapCenter - 221644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221644]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02684_not_prime : ¬(recordGapCenter - 221458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221458]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02685_not_prime : ¬(recordGapCenter - 221332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221332]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02686_not_prime : ¬(recordGapCenter - 221218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221218]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02687_not_prime : ¬(recordGapCenter - 221164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221164]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

theorem fullRecordGapTerm02688_not_prime : ¬(recordGapCenter - 220882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220882]
  · apply fullRecordGapRow00042_fermat
    simp [fullRecordGapRow00042_values]

end PrimeFactorUnimodality
