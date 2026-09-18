import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00093_values : List Nat :=
  [fullRecordGapCenterValue + 306518,
    fullRecordGapCenterValue + 306542,
    fullRecordGapCenterValue + 306668,
    fullRecordGapCenterValue + 306686,
    fullRecordGapCenterValue + 306692,
    fullRecordGapCenterValue + 306716,
    fullRecordGapCenterValue + 306798,
    fullRecordGapCenterValue + 306932,
    fullRecordGapCenterValue + 307158,
    fullRecordGapCenterValue + 307178,
    fullRecordGapCenterValue + 307302,
    fullRecordGapCenterValue + 307328,
    fullRecordGapCenterValue + 307388,
    fullRecordGapCenterValue + 307478,
    fullRecordGapCenterValue + 307526,
    fullRecordGapCenterValue + 307652,
    fullRecordGapCenterValue + 307676,
    fullRecordGapCenterValue + 307682,
    fullRecordGapCenterValue + 307722,
    fullRecordGapCenterValue + 307778,
    fullRecordGapCenterValue + 307982,
    fullRecordGapCenterValue + 308000,
    fullRecordGapCenterValue + 308012,
    fullRecordGapCenterValue + 308276,
    fullRecordGapCenterValue + 308372,
    fullRecordGapCenterValue + 308442,
    fullRecordGapCenterValue + 308486,
    fullRecordGapCenterValue + 308838,
    fullRecordGapCenterValue + 308886,
    fullRecordGapCenterValue + 308996,
    fullRecordGapCenterValue + 309002,
    fullRecordGapCenterValue + 309086,
    fullRecordGapCenterValue + 309102,
    fullRecordGapCenterValue + 309146,
    fullRecordGapCenterValue + 309242,
    fullRecordGapCenterValue + 309306,
    fullRecordGapCenterValue + 309446,
    fullRecordGapCenterValue + 309578,
    fullRecordGapCenterValue + 309746,
    fullRecordGapCenterValue + 309786,
    fullRecordGapCenterValue + 309788,
    fullRecordGapCenterValue + 309908,
    fullRecordGapCenterValue + 310052,
    fullRecordGapCenterValue + 310166,
    fullRecordGapCenterValue + 310238,
    fullRecordGapCenterValue + 310322,
    fullRecordGapCenterValue + 310326,
    fullRecordGapCenterValue + 310382,
    fullRecordGapCenterValue + 310406,
    fullRecordGapCenterValue + 310502,
    fullRecordGapCenterValue + 310538,
    fullRecordGapCenterValue + 310602,
    fullRecordGapCenterValue + 310748,
    fullRecordGapCenterValue + 310782,
    fullRecordGapCenterValue + 310796,
    fullRecordGapCenterValue + 310818,
    fullRecordGapCenterValue + 310886,
    fullRecordGapCenterValue + 310962,
    fullRecordGapCenterValue + 311018,
    fullRecordGapCenterValue + 311042,
    fullRecordGapCenterValue + 311342,
    fullRecordGapCenterValue + 311358,
    fullRecordGapCenterValue + 311396,
    fullRecordGapCenterValue + 311442]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00093_fermat : ∀ n ∈ fullRecordGapRow00093_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05889_not_prime : ¬(recordGapCenter + 306518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 306518]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05890_not_prime : ¬(recordGapCenter + 306542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 306542]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05891_not_prime : ¬(recordGapCenter + 306668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 306668]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05892_not_prime : ¬(recordGapCenter + 306686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 306686]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05893_not_prime : ¬(recordGapCenter + 306692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 306692]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05894_not_prime : ¬(recordGapCenter + 306716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 306716]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05895_not_prime : ¬(recordGapCenter + 306798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 306798]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05896_not_prime : ¬(recordGapCenter + 306932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 306932]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05897_not_prime : ¬(recordGapCenter + 307158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 307158]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05898_not_prime : ¬(recordGapCenter + 307178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 307178]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05899_not_prime : ¬(recordGapCenter + 307302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 307302]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05900_not_prime : ¬(recordGapCenter + 307328).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 307328]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05901_not_prime : ¬(recordGapCenter + 307388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 307388]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05902_not_prime : ¬(recordGapCenter + 307478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 307478]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05903_not_prime : ¬(recordGapCenter + 307526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 307526]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05904_not_prime : ¬(recordGapCenter + 307652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 307652]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05905_not_prime : ¬(recordGapCenter + 307676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 307676]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05906_not_prime : ¬(recordGapCenter + 307682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 307682]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05907_not_prime : ¬(recordGapCenter + 307722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 307722]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05908_not_prime : ¬(recordGapCenter + 307778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 307778]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05909_not_prime : ¬(recordGapCenter + 307982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 307982]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05910_not_prime : ¬(recordGapCenter + 308000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 308000]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05911_not_prime : ¬(recordGapCenter + 308012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 308012]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05912_not_prime : ¬(recordGapCenter + 308276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 308276]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05913_not_prime : ¬(recordGapCenter + 308372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 308372]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05914_not_prime : ¬(recordGapCenter + 308442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 308442]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05915_not_prime : ¬(recordGapCenter + 308486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 308486]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05916_not_prime : ¬(recordGapCenter + 308838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 308838]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05917_not_prime : ¬(recordGapCenter + 308886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 308886]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05918_not_prime : ¬(recordGapCenter + 308996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 308996]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05919_not_prime : ¬(recordGapCenter + 309002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 309002]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05920_not_prime : ¬(recordGapCenter + 309086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 309086]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05921_not_prime : ¬(recordGapCenter + 309102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 309102]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05922_not_prime : ¬(recordGapCenter + 309146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 309146]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05923_not_prime : ¬(recordGapCenter + 309242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 309242]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05924_not_prime : ¬(recordGapCenter + 309306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 309306]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05925_not_prime : ¬(recordGapCenter + 309446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 309446]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05926_not_prime : ¬(recordGapCenter + 309578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 309578]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05927_not_prime : ¬(recordGapCenter + 309746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 309746]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05928_not_prime : ¬(recordGapCenter + 309786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 309786]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05929_not_prime : ¬(recordGapCenter + 309788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 309788]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05930_not_prime : ¬(recordGapCenter + 309908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 309908]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05931_not_prime : ¬(recordGapCenter + 310052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310052]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05932_not_prime : ¬(recordGapCenter + 310166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310166]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05933_not_prime : ¬(recordGapCenter + 310238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310238]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05934_not_prime : ¬(recordGapCenter + 310322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310322]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05935_not_prime : ¬(recordGapCenter + 310326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310326]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05936_not_prime : ¬(recordGapCenter + 310382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310382]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05937_not_prime : ¬(recordGapCenter + 310406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310406]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05938_not_prime : ¬(recordGapCenter + 310502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310502]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05939_not_prime : ¬(recordGapCenter + 310538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310538]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05940_not_prime : ¬(recordGapCenter + 310602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310602]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05941_not_prime : ¬(recordGapCenter + 310748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310748]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05942_not_prime : ¬(recordGapCenter + 310782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310782]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05943_not_prime : ¬(recordGapCenter + 310796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310796]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05944_not_prime : ¬(recordGapCenter + 310818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310818]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05945_not_prime : ¬(recordGapCenter + 310886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310886]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05946_not_prime : ¬(recordGapCenter + 310962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 310962]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05947_not_prime : ¬(recordGapCenter + 311018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 311018]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05948_not_prime : ¬(recordGapCenter + 311042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 311042]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05949_not_prime : ¬(recordGapCenter + 311342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 311342]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05950_not_prime : ¬(recordGapCenter + 311358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 311358]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05951_not_prime : ¬(recordGapCenter + 311396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 311396]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

theorem fullRecordGapTerm05952_not_prime : ¬(recordGapCenter + 311442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 311442]
  · apply fullRecordGapRow00093_fermat
    simp [fullRecordGapRow00093_values]

end PrimeFactorUnimodality
