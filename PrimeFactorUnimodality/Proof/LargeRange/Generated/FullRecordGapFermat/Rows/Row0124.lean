import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00124_values : List Nat :=
  [fullRecordGapCenterValue + 460766,
    fullRecordGapCenterValue + 460778,
    fullRecordGapCenterValue + 460800,
    fullRecordGapCenterValue + 460806,
    fullRecordGapCenterValue + 460992,
    fullRecordGapCenterValue + 461030,
    fullRecordGapCenterValue + 461078,
    fullRecordGapCenterValue + 461192,
    fullRecordGapCenterValue + 461298,
    fullRecordGapCenterValue + 461366,
    fullRecordGapCenterValue + 461372,
    fullRecordGapCenterValue + 461478,
    fullRecordGapCenterValue + 461546,
    fullRecordGapCenterValue + 461658,
    fullRecordGapCenterValue + 461672,
    fullRecordGapCenterValue + 461766,
    fullRecordGapCenterValue + 461778,
    fullRecordGapCenterValue + 461858,
    fullRecordGapCenterValue + 461882,
    fullRecordGapCenterValue + 461946,
    fullRecordGapCenterValue + 462000,
    fullRecordGapCenterValue + 462002,
    fullRecordGapCenterValue + 462008,
    fullRecordGapCenterValue + 462102,
    fullRecordGapCenterValue + 462138,
    fullRecordGapCenterValue + 462158,
    fullRecordGapCenterValue + 462248,
    fullRecordGapCenterValue + 462290,
    fullRecordGapCenterValue + 462446,
    fullRecordGapCenterValue + 462452,
    fullRecordGapCenterValue + 462542,
    fullRecordGapCenterValue + 462558,
    fullRecordGapCenterValue + 462578,
    fullRecordGapCenterValue + 462698,
    fullRecordGapCenterValue + 462758,
    fullRecordGapCenterValue + 462918,
    fullRecordGapCenterValue + 462926,
    fullRecordGapCenterValue + 462962,
    fullRecordGapCenterValue + 463010,
    fullRecordGapCenterValue + 463026,
    fullRecordGapCenterValue + 463050,
    fullRecordGapCenterValue + 463076,
    fullRecordGapCenterValue + 463142,
    fullRecordGapCenterValue + 463178,
    fullRecordGapCenterValue + 463226,
    fullRecordGapCenterValue + 463278,
    fullRecordGapCenterValue + 463286,
    fullRecordGapCenterValue + 463412,
    fullRecordGapCenterValue + 463422,
    fullRecordGapCenterValue + 463458,
    fullRecordGapCenterValue + 463566,
    fullRecordGapCenterValue + 463578,
    fullRecordGapCenterValue + 463598,
    fullRecordGapCenterValue + 463886,
    fullRecordGapCenterValue + 463902,
    fullRecordGapCenterValue + 463916,
    fullRecordGapCenterValue + 463922,
    fullRecordGapCenterValue + 464258,
    fullRecordGapCenterValue + 464378,
    fullRecordGapCenterValue + 464510,
    fullRecordGapCenterValue + 464606,
    fullRecordGapCenterValue + 464640,
    fullRecordGapCenterValue + 464682,
    fullRecordGapCenterValue + 464726]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00124_fermat : ∀ n ∈ fullRecordGapRow00124_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07873_not_prime : ¬(recordGapCenter + 460766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460766]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07874_not_prime : ¬(recordGapCenter + 460778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460778]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07875_not_prime : ¬(recordGapCenter + 460800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460800]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07876_not_prime : ¬(recordGapCenter + 460806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460806]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07877_not_prime : ¬(recordGapCenter + 460992).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 460992]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07878_not_prime : ¬(recordGapCenter + 461030).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461030]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07879_not_prime : ¬(recordGapCenter + 461078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461078]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07880_not_prime : ¬(recordGapCenter + 461192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461192]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07881_not_prime : ¬(recordGapCenter + 461298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461298]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07882_not_prime : ¬(recordGapCenter + 461366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461366]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07883_not_prime : ¬(recordGapCenter + 461372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461372]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07884_not_prime : ¬(recordGapCenter + 461478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461478]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07885_not_prime : ¬(recordGapCenter + 461546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461546]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07886_not_prime : ¬(recordGapCenter + 461658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461658]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07887_not_prime : ¬(recordGapCenter + 461672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461672]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07888_not_prime : ¬(recordGapCenter + 461766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461766]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07889_not_prime : ¬(recordGapCenter + 461778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461778]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07890_not_prime : ¬(recordGapCenter + 461858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461858]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07891_not_prime : ¬(recordGapCenter + 461882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461882]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07892_not_prime : ¬(recordGapCenter + 461946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 461946]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07893_not_prime : ¬(recordGapCenter + 462000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462000]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07894_not_prime : ¬(recordGapCenter + 462002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462002]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07895_not_prime : ¬(recordGapCenter + 462008).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462008]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07896_not_prime : ¬(recordGapCenter + 462102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462102]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07897_not_prime : ¬(recordGapCenter + 462138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462138]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07898_not_prime : ¬(recordGapCenter + 462158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462158]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07899_not_prime : ¬(recordGapCenter + 462248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462248]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07900_not_prime : ¬(recordGapCenter + 462290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462290]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07901_not_prime : ¬(recordGapCenter + 462446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462446]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07902_not_prime : ¬(recordGapCenter + 462452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462452]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07903_not_prime : ¬(recordGapCenter + 462542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462542]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07904_not_prime : ¬(recordGapCenter + 462558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462558]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07905_not_prime : ¬(recordGapCenter + 462578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462578]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07906_not_prime : ¬(recordGapCenter + 462698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462698]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07907_not_prime : ¬(recordGapCenter + 462758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462758]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07908_not_prime : ¬(recordGapCenter + 462918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462918]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07909_not_prime : ¬(recordGapCenter + 462926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462926]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07910_not_prime : ¬(recordGapCenter + 462962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 462962]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07911_not_prime : ¬(recordGapCenter + 463010).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463010]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07912_not_prime : ¬(recordGapCenter + 463026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463026]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07913_not_prime : ¬(recordGapCenter + 463050).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463050]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07914_not_prime : ¬(recordGapCenter + 463076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463076]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07915_not_prime : ¬(recordGapCenter + 463142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463142]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07916_not_prime : ¬(recordGapCenter + 463178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463178]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07917_not_prime : ¬(recordGapCenter + 463226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463226]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07918_not_prime : ¬(recordGapCenter + 463278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463278]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07919_not_prime : ¬(recordGapCenter + 463286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463286]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07920_not_prime : ¬(recordGapCenter + 463412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463412]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07921_not_prime : ¬(recordGapCenter + 463422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463422]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07922_not_prime : ¬(recordGapCenter + 463458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463458]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07923_not_prime : ¬(recordGapCenter + 463566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463566]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07924_not_prime : ¬(recordGapCenter + 463578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463578]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07925_not_prime : ¬(recordGapCenter + 463598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463598]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07926_not_prime : ¬(recordGapCenter + 463886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463886]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07927_not_prime : ¬(recordGapCenter + 463902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463902]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07928_not_prime : ¬(recordGapCenter + 463916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463916]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07929_not_prime : ¬(recordGapCenter + 463922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 463922]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07930_not_prime : ¬(recordGapCenter + 464258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 464258]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07931_not_prime : ¬(recordGapCenter + 464378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 464378]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07932_not_prime : ¬(recordGapCenter + 464510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 464510]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07933_not_prime : ¬(recordGapCenter + 464606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 464606]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07934_not_prime : ¬(recordGapCenter + 464640).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 464640]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07935_not_prime : ¬(recordGapCenter + 464682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 464682]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

theorem fullRecordGapTerm07936_not_prime : ¬(recordGapCenter + 464726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 464726]
  · apply fullRecordGapRow00124_fermat
    simp [fullRecordGapRow00124_values]

end PrimeFactorUnimodality
