import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00126_values : List Nat :=
  [fullRecordGapCenterValue + 468956,
    fullRecordGapCenterValue + 469002,
    fullRecordGapCenterValue + 469178,
    fullRecordGapCenterValue + 469226,
    fullRecordGapCenterValue + 469316,
    fullRecordGapCenterValue + 469466,
    fullRecordGapCenterValue + 469562,
    fullRecordGapCenterValue + 469598,
    fullRecordGapCenterValue + 469688,
    fullRecordGapCenterValue + 469698,
    fullRecordGapCenterValue + 469866,
    fullRecordGapCenterValue + 469922,
    fullRecordGapCenterValue + 469928,
    fullRecordGapCenterValue + 470012,
    fullRecordGapCenterValue + 470046,
    fullRecordGapCenterValue + 470082,
    fullRecordGapCenterValue + 470102,
    fullRecordGapCenterValue + 470138,
    fullRecordGapCenterValue + 470198,
    fullRecordGapCenterValue + 470222,
    fullRecordGapCenterValue + 470342,
    fullRecordGapCenterValue + 470486,
    fullRecordGapCenterValue + 470570,
    fullRecordGapCenterValue + 470636,
    fullRecordGapCenterValue + 470648,
    fullRecordGapCenterValue + 470870,
    fullRecordGapCenterValue + 470978,
    fullRecordGapCenterValue + 470982,
    fullRecordGapCenterValue + 471066,
    fullRecordGapCenterValue + 471110,
    fullRecordGapCenterValue + 471116,
    fullRecordGapCenterValue + 471182,
    fullRecordGapCenterValue + 471326,
    fullRecordGapCenterValue + 471332,
    fullRecordGapCenterValue + 471446,
    fullRecordGapCenterValue + 471578,
    fullRecordGapCenterValue + 471902,
    fullRecordGapCenterValue + 471908,
    fullRecordGapCenterValue + 472070,
    fullRecordGapCenterValue + 472106,
    fullRecordGapCenterValue + 472148,
    fullRecordGapCenterValue + 472286,
    fullRecordGapCenterValue + 472326,
    fullRecordGapCenterValue + 472418,
    fullRecordGapCenterValue + 472500,
    fullRecordGapCenterValue + 472586,
    fullRecordGapCenterValue + 472658,
    fullRecordGapCenterValue + 472818,
    fullRecordGapCenterValue + 472922,
    fullRecordGapCenterValue + 472938,
    fullRecordGapCenterValue + 472988,
    fullRecordGapCenterValue + 473006,
    fullRecordGapCenterValue + 473118,
    fullRecordGapCenterValue + 473126,
    fullRecordGapCenterValue + 473142,
    fullRecordGapCenterValue + 473322,
    fullRecordGapCenterValue + 473372,
    fullRecordGapCenterValue + 473498,
    fullRecordGapCenterValue + 473510,
    fullRecordGapCenterValue + 473576,
    fullRecordGapCenterValue + 473630,
    fullRecordGapCenterValue + 473768,
    fullRecordGapCenterValue + 473862,
    fullRecordGapCenterValue + 474038]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00126_fermat : ∀ n ∈ fullRecordGapRow00126_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08001_not_prime : ¬(recordGapCenter + 468956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468956]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08002_not_prime : ¬(recordGapCenter + 469002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469002]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08003_not_prime : ¬(recordGapCenter + 469178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469178]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08004_not_prime : ¬(recordGapCenter + 469226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469226]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08005_not_prime : ¬(recordGapCenter + 469316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469316]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08006_not_prime : ¬(recordGapCenter + 469466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469466]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08007_not_prime : ¬(recordGapCenter + 469562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469562]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08008_not_prime : ¬(recordGapCenter + 469598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469598]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08009_not_prime : ¬(recordGapCenter + 469688).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469688]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08010_not_prime : ¬(recordGapCenter + 469698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469698]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08011_not_prime : ¬(recordGapCenter + 469866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469866]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08012_not_prime : ¬(recordGapCenter + 469922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469922]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08013_not_prime : ¬(recordGapCenter + 469928).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469928]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08014_not_prime : ¬(recordGapCenter + 470012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470012]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08015_not_prime : ¬(recordGapCenter + 470046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470046]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08016_not_prime : ¬(recordGapCenter + 470082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470082]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08017_not_prime : ¬(recordGapCenter + 470102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470102]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08018_not_prime : ¬(recordGapCenter + 470138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470138]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08019_not_prime : ¬(recordGapCenter + 470198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470198]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08020_not_prime : ¬(recordGapCenter + 470222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470222]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08021_not_prime : ¬(recordGapCenter + 470342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470342]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08022_not_prime : ¬(recordGapCenter + 470486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470486]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08023_not_prime : ¬(recordGapCenter + 470570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470570]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08024_not_prime : ¬(recordGapCenter + 470636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470636]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08025_not_prime : ¬(recordGapCenter + 470648).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470648]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08026_not_prime : ¬(recordGapCenter + 470870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470870]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08027_not_prime : ¬(recordGapCenter + 470978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470978]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08028_not_prime : ¬(recordGapCenter + 470982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470982]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08029_not_prime : ¬(recordGapCenter + 471066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471066]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08030_not_prime : ¬(recordGapCenter + 471110).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471110]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08031_not_prime : ¬(recordGapCenter + 471116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471116]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08032_not_prime : ¬(recordGapCenter + 471182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471182]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08033_not_prime : ¬(recordGapCenter + 471326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471326]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08034_not_prime : ¬(recordGapCenter + 471332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471332]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08035_not_prime : ¬(recordGapCenter + 471446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471446]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08036_not_prime : ¬(recordGapCenter + 471578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471578]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08037_not_prime : ¬(recordGapCenter + 471902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471902]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08038_not_prime : ¬(recordGapCenter + 471908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471908]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08039_not_prime : ¬(recordGapCenter + 472070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472070]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08040_not_prime : ¬(recordGapCenter + 472106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472106]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08041_not_prime : ¬(recordGapCenter + 472148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472148]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08042_not_prime : ¬(recordGapCenter + 472286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472286]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08043_not_prime : ¬(recordGapCenter + 472326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472326]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08044_not_prime : ¬(recordGapCenter + 472418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472418]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08045_not_prime : ¬(recordGapCenter + 472500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472500]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08046_not_prime : ¬(recordGapCenter + 472586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472586]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08047_not_prime : ¬(recordGapCenter + 472658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472658]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08048_not_prime : ¬(recordGapCenter + 472818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472818]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08049_not_prime : ¬(recordGapCenter + 472922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472922]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08050_not_prime : ¬(recordGapCenter + 472938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472938]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08051_not_prime : ¬(recordGapCenter + 472988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472988]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08052_not_prime : ¬(recordGapCenter + 473006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473006]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08053_not_prime : ¬(recordGapCenter + 473118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473118]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08054_not_prime : ¬(recordGapCenter + 473126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473126]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08055_not_prime : ¬(recordGapCenter + 473142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473142]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08056_not_prime : ¬(recordGapCenter + 473322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473322]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08057_not_prime : ¬(recordGapCenter + 473372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473372]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08058_not_prime : ¬(recordGapCenter + 473498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473498]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08059_not_prime : ¬(recordGapCenter + 473510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473510]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08060_not_prime : ¬(recordGapCenter + 473576).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473576]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08061_not_prime : ¬(recordGapCenter + 473630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473630]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08062_not_prime : ¬(recordGapCenter + 473768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473768]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08063_not_prime : ¬(recordGapCenter + 473862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473862]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

theorem fullRecordGapTerm08064_not_prime : ¬(recordGapCenter + 474038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474038]
  · apply fullRecordGapRow00126_fermat
    simp [fullRecordGapRow00126_values]

end PrimeFactorUnimodality
