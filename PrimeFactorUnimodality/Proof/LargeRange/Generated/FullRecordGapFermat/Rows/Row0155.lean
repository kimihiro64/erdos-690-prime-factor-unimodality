import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00155_values : List Nat :=
  [fullRecordGapCenterValue + 592386,
    fullRecordGapCenterValue + 592422,
    fullRecordGapCenterValue + 592442,
    fullRecordGapCenterValue + 592502,
    fullRecordGapCenterValue + 592568,
    fullRecordGapCenterValue + 592616,
    fullRecordGapCenterValue + 592638,
    fullRecordGapCenterValue + 592716,
    fullRecordGapCenterValue + 592730,
    fullRecordGapCenterValue + 592842,
    fullRecordGapCenterValue + 592916,
    fullRecordGapCenterValue + 592932,
    fullRecordGapCenterValue + 593022,
    fullRecordGapCenterValue + 593048,
    fullRecordGapCenterValue + 593192,
    fullRecordGapCenterValue + 593330,
    fullRecordGapCenterValue + 593426,
    fullRecordGapCenterValue + 593498,
    fullRecordGapCenterValue + 593546,
    fullRecordGapCenterValue + 593562,
    fullRecordGapCenterValue + 593576,
    fullRecordGapCenterValue + 593612,
    fullRecordGapCenterValue + 593672,
    fullRecordGapCenterValue + 593756,
    fullRecordGapCenterValue + 593772,
    fullRecordGapCenterValue + 593778,
    fullRecordGapCenterValue + 593828,
    fullRecordGapCenterValue + 593876,
    fullRecordGapCenterValue + 593990,
    fullRecordGapCenterValue + 594102,
    fullRecordGapCenterValue + 594276,
    fullRecordGapCenterValue + 594296,
    fullRecordGapCenterValue + 594318,
    fullRecordGapCenterValue + 594372,
    fullRecordGapCenterValue + 594470,
    fullRecordGapCenterValue + 594618,
    fullRecordGapCenterValue + 594708,
    fullRecordGapCenterValue + 594842,
    fullRecordGapCenterValue + 594938,
    fullRecordGapCenterValue + 594962,
    fullRecordGapCenterValue + 595172,
    fullRecordGapCenterValue + 595178,
    fullRecordGapCenterValue + 595226,
    fullRecordGapCenterValue + 595268,
    fullRecordGapCenterValue + 595352,
    fullRecordGapCenterValue + 595436,
    fullRecordGapCenterValue + 595446,
    fullRecordGapCenterValue + 595542,
    fullRecordGapCenterValue + 595592,
    fullRecordGapCenterValue + 595610,
    fullRecordGapCenterValue + 595652,
    fullRecordGapCenterValue + 595670,
    fullRecordGapCenterValue + 595796,
    fullRecordGapCenterValue + 595956,
    fullRecordGapCenterValue + 596072,
    fullRecordGapCenterValue + 596186,
    fullRecordGapCenterValue + 596202,
    fullRecordGapCenterValue + 596216,
    fullRecordGapCenterValue + 596226,
    fullRecordGapCenterValue + 596276,
    fullRecordGapCenterValue + 596288,
    fullRecordGapCenterValue + 596346,
    fullRecordGapCenterValue + 596348,
    fullRecordGapCenterValue + 596382]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00155_fermat : ∀ n ∈ fullRecordGapRow00155_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09857_not_prime : ¬(recordGapCenter + 592386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592386]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09858_not_prime : ¬(recordGapCenter + 592422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592422]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09859_not_prime : ¬(recordGapCenter + 592442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592442]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09860_not_prime : ¬(recordGapCenter + 592502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592502]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09861_not_prime : ¬(recordGapCenter + 592568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592568]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09862_not_prime : ¬(recordGapCenter + 592616).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592616]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09863_not_prime : ¬(recordGapCenter + 592638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592638]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09864_not_prime : ¬(recordGapCenter + 592716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592716]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09865_not_prime : ¬(recordGapCenter + 592730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592730]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09866_not_prime : ¬(recordGapCenter + 592842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592842]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09867_not_prime : ¬(recordGapCenter + 592916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592916]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09868_not_prime : ¬(recordGapCenter + 592932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 592932]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09869_not_prime : ¬(recordGapCenter + 593022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593022]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09870_not_prime : ¬(recordGapCenter + 593048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593048]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09871_not_prime : ¬(recordGapCenter + 593192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593192]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09872_not_prime : ¬(recordGapCenter + 593330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593330]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09873_not_prime : ¬(recordGapCenter + 593426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593426]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09874_not_prime : ¬(recordGapCenter + 593498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593498]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09875_not_prime : ¬(recordGapCenter + 593546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593546]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09876_not_prime : ¬(recordGapCenter + 593562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593562]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09877_not_prime : ¬(recordGapCenter + 593576).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593576]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09878_not_prime : ¬(recordGapCenter + 593612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593612]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09879_not_prime : ¬(recordGapCenter + 593672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593672]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09880_not_prime : ¬(recordGapCenter + 593756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593756]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09881_not_prime : ¬(recordGapCenter + 593772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593772]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09882_not_prime : ¬(recordGapCenter + 593778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593778]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09883_not_prime : ¬(recordGapCenter + 593828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593828]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09884_not_prime : ¬(recordGapCenter + 593876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593876]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09885_not_prime : ¬(recordGapCenter + 593990).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 593990]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09886_not_prime : ¬(recordGapCenter + 594102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 594102]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09887_not_prime : ¬(recordGapCenter + 594276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 594276]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09888_not_prime : ¬(recordGapCenter + 594296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 594296]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09889_not_prime : ¬(recordGapCenter + 594318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 594318]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09890_not_prime : ¬(recordGapCenter + 594372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 594372]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09891_not_prime : ¬(recordGapCenter + 594470).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 594470]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09892_not_prime : ¬(recordGapCenter + 594618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 594618]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09893_not_prime : ¬(recordGapCenter + 594708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 594708]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09894_not_prime : ¬(recordGapCenter + 594842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 594842]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09895_not_prime : ¬(recordGapCenter + 594938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 594938]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09896_not_prime : ¬(recordGapCenter + 594962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 594962]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09897_not_prime : ¬(recordGapCenter + 595172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 595172]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09898_not_prime : ¬(recordGapCenter + 595178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 595178]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09899_not_prime : ¬(recordGapCenter + 595226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 595226]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09900_not_prime : ¬(recordGapCenter + 595268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 595268]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09901_not_prime : ¬(recordGapCenter + 595352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 595352]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09902_not_prime : ¬(recordGapCenter + 595436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 595436]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09903_not_prime : ¬(recordGapCenter + 595446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 595446]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09904_not_prime : ¬(recordGapCenter + 595542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 595542]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09905_not_prime : ¬(recordGapCenter + 595592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 595592]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09906_not_prime : ¬(recordGapCenter + 595610).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 595610]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09907_not_prime : ¬(recordGapCenter + 595652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 595652]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09908_not_prime : ¬(recordGapCenter + 595670).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 595670]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09909_not_prime : ¬(recordGapCenter + 595796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 595796]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09910_not_prime : ¬(recordGapCenter + 595956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 595956]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09911_not_prime : ¬(recordGapCenter + 596072).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596072]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09912_not_prime : ¬(recordGapCenter + 596186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596186]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09913_not_prime : ¬(recordGapCenter + 596202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596202]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09914_not_prime : ¬(recordGapCenter + 596216).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596216]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09915_not_prime : ¬(recordGapCenter + 596226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596226]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09916_not_prime : ¬(recordGapCenter + 596276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596276]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09917_not_prime : ¬(recordGapCenter + 596288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596288]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09918_not_prime : ¬(recordGapCenter + 596346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596346]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09919_not_prime : ¬(recordGapCenter + 596348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596348]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

theorem fullRecordGapTerm09920_not_prime : ¬(recordGapCenter + 596382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596382]
  · apply fullRecordGapRow00155_fermat
    simp [fullRecordGapRow00155_values]

end PrimeFactorUnimodality
