import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00001_values : List Nat :=
  [fullRecordGapCenterValue - 455622,
    fullRecordGapCenterValue - 455458,
    fullRecordGapCenterValue - 455410,
    fullRecordGapCenterValue - 455368,
    fullRecordGapCenterValue - 455298,
    fullRecordGapCenterValue - 455254,
    fullRecordGapCenterValue - 455214,
    fullRecordGapCenterValue - 455194,
    fullRecordGapCenterValue - 454984,
    fullRecordGapCenterValue - 454978,
    fullRecordGapCenterValue - 454782,
    fullRecordGapCenterValue - 454758,
    fullRecordGapCenterValue - 454732,
    fullRecordGapCenterValue - 454492,
    fullRecordGapCenterValue - 454330,
    fullRecordGapCenterValue - 454270,
    fullRecordGapCenterValue - 454264,
    fullRecordGapCenterValue - 454242,
    fullRecordGapCenterValue - 454228,
    fullRecordGapCenterValue - 454218,
    fullRecordGapCenterValue - 454074,
    fullRecordGapCenterValue - 454054,
    fullRecordGapCenterValue - 453982,
    fullRecordGapCenterValue - 453954,
    fullRecordGapCenterValue - 453802,
    fullRecordGapCenterValue - 453448,
    fullRecordGapCenterValue - 453318,
    fullRecordGapCenterValue - 453234,
    fullRecordGapCenterValue - 453198,
    fullRecordGapCenterValue - 453162,
    fullRecordGapCenterValue - 453148,
    fullRecordGapCenterValue - 453018,
    fullRecordGapCenterValue - 452932,
    fullRecordGapCenterValue - 452668,
    fullRecordGapCenterValue - 452644,
    fullRecordGapCenterValue - 452442,
    fullRecordGapCenterValue - 452344,
    fullRecordGapCenterValue - 452262,
    fullRecordGapCenterValue - 452248,
    fullRecordGapCenterValue - 452044,
    fullRecordGapCenterValue - 452002,
    fullRecordGapCenterValue - 451978,
    fullRecordGapCenterValue - 451842,
    fullRecordGapCenterValue - 451810,
    fullRecordGapCenterValue - 451734,
    fullRecordGapCenterValue - 451678,
    fullRecordGapCenterValue - 451614,
    fullRecordGapCenterValue - 451534,
    fullRecordGapCenterValue - 451372,
    fullRecordGapCenterValue - 451342,
    fullRecordGapCenterValue - 451302,
    fullRecordGapCenterValue - 451258,
    fullRecordGapCenterValue - 451254,
    fullRecordGapCenterValue - 451138,
    fullRecordGapCenterValue - 451054,
    fullRecordGapCenterValue - 450958,
    fullRecordGapCenterValue - 450922,
    fullRecordGapCenterValue - 450798,
    fullRecordGapCenterValue - 450742,
    fullRecordGapCenterValue - 450628,
    fullRecordGapCenterValue - 450610,
    fullRecordGapCenterValue - 450442,
    fullRecordGapCenterValue - 450412,
    fullRecordGapCenterValue - 450298]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00001_fermat : ∀ n ∈ fullRecordGapRow00001_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00001_not_prime : ¬(recordGapCenter - 455622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 455622]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00002_not_prime : ¬(recordGapCenter - 455458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 455458]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00003_not_prime : ¬(recordGapCenter - 455410).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 455410]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00004_not_prime : ¬(recordGapCenter - 455368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 455368]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00005_not_prime : ¬(recordGapCenter - 455298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 455298]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00006_not_prime : ¬(recordGapCenter - 455254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 455254]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00007_not_prime : ¬(recordGapCenter - 455214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 455214]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00008_not_prime : ¬(recordGapCenter - 455194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 455194]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00009_not_prime : ¬(recordGapCenter - 454984).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 454984]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00010_not_prime : ¬(recordGapCenter - 454978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 454978]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00011_not_prime : ¬(recordGapCenter - 454782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 454782]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00012_not_prime : ¬(recordGapCenter - 454758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 454758]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00013_not_prime : ¬(recordGapCenter - 454732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 454732]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00014_not_prime : ¬(recordGapCenter - 454492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 454492]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00015_not_prime : ¬(recordGapCenter - 454330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 454330]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00016_not_prime : ¬(recordGapCenter - 454270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 454270]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00017_not_prime : ¬(recordGapCenter - 454264).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 454264]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00018_not_prime : ¬(recordGapCenter - 454242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 454242]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00019_not_prime : ¬(recordGapCenter - 454228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 454228]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00020_not_prime : ¬(recordGapCenter - 454218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 454218]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00021_not_prime : ¬(recordGapCenter - 454074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 454074]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00022_not_prime : ¬(recordGapCenter - 454054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 454054]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00023_not_prime : ¬(recordGapCenter - 453982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 453982]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00024_not_prime : ¬(recordGapCenter - 453954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 453954]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00025_not_prime : ¬(recordGapCenter - 453802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 453802]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00026_not_prime : ¬(recordGapCenter - 453448).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 453448]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00027_not_prime : ¬(recordGapCenter - 453318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 453318]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00028_not_prime : ¬(recordGapCenter - 453234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 453234]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00029_not_prime : ¬(recordGapCenter - 453198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 453198]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00030_not_prime : ¬(recordGapCenter - 453162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 453162]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00031_not_prime : ¬(recordGapCenter - 453148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 453148]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00032_not_prime : ¬(recordGapCenter - 453018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 453018]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00033_not_prime : ¬(recordGapCenter - 452932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 452932]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00034_not_prime : ¬(recordGapCenter - 452668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 452668]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00035_not_prime : ¬(recordGapCenter - 452644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 452644]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00036_not_prime : ¬(recordGapCenter - 452442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 452442]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00037_not_prime : ¬(recordGapCenter - 452344).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 452344]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00038_not_prime : ¬(recordGapCenter - 452262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 452262]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00039_not_prime : ¬(recordGapCenter - 452248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 452248]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00040_not_prime : ¬(recordGapCenter - 452044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 452044]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00041_not_prime : ¬(recordGapCenter - 452002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 452002]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00042_not_prime : ¬(recordGapCenter - 451978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 451978]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00043_not_prime : ¬(recordGapCenter - 451842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 451842]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00044_not_prime : ¬(recordGapCenter - 451810).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 451810]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00045_not_prime : ¬(recordGapCenter - 451734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 451734]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00046_not_prime : ¬(recordGapCenter - 451678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 451678]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00047_not_prime : ¬(recordGapCenter - 451614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 451614]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00048_not_prime : ¬(recordGapCenter - 451534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 451534]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00049_not_prime : ¬(recordGapCenter - 451372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 451372]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00050_not_prime : ¬(recordGapCenter - 451342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 451342]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00051_not_prime : ¬(recordGapCenter - 451302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 451302]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00052_not_prime : ¬(recordGapCenter - 451258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 451258]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00053_not_prime : ¬(recordGapCenter - 451254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 451254]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00054_not_prime : ¬(recordGapCenter - 451138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 451138]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00055_not_prime : ¬(recordGapCenter - 451054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 451054]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00056_not_prime : ¬(recordGapCenter - 450958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450958]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00057_not_prime : ¬(recordGapCenter - 450922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450922]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00058_not_prime : ¬(recordGapCenter - 450798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450798]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00059_not_prime : ¬(recordGapCenter - 450742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450742]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00060_not_prime : ¬(recordGapCenter - 450628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450628]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00061_not_prime : ¬(recordGapCenter - 450610).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450610]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00062_not_prime : ¬(recordGapCenter - 450442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450442]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00063_not_prime : ¬(recordGapCenter - 450412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450412]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

theorem fullRecordGapTerm00064_not_prime : ¬(recordGapCenter - 450298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450298]
  · apply fullRecordGapRow00001_fermat
    simp [fullRecordGapRow00001_values]

end PrimeFactorUnimodality
