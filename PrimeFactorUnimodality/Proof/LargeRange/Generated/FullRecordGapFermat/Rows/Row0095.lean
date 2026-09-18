import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00095_values : List Nat :=
  [fullRecordGapCenterValue + 316898,
    fullRecordGapCenterValue + 316932,
    fullRecordGapCenterValue + 317166,
    fullRecordGapCenterValue + 317276,
    fullRecordGapCenterValue + 317298,
    fullRecordGapCenterValue + 317396,
    fullRecordGapCenterValue + 317406,
    fullRecordGapCenterValue + 317468,
    fullRecordGapCenterValue + 317516,
    fullRecordGapCenterValue + 317886,
    fullRecordGapCenterValue + 317972,
    fullRecordGapCenterValue + 318026,
    fullRecordGapCenterValue + 318102,
    fullRecordGapCenterValue + 318158,
    fullRecordGapCenterValue + 318398,
    fullRecordGapCenterValue + 318462,
    fullRecordGapCenterValue + 318558,
    fullRecordGapCenterValue + 318722,
    fullRecordGapCenterValue + 318788,
    fullRecordGapCenterValue + 318806,
    fullRecordGapCenterValue + 318938,
    fullRecordGapCenterValue + 318966,
    fullRecordGapCenterValue + 319028,
    fullRecordGapCenterValue + 319082,
    fullRecordGapCenterValue + 319182,
    fullRecordGapCenterValue + 319268,
    fullRecordGapCenterValue + 319386,
    fullRecordGapCenterValue + 319628,
    fullRecordGapCenterValue + 319686,
    fullRecordGapCenterValue + 319742,
    fullRecordGapCenterValue + 319916,
    fullRecordGapCenterValue + 319938,
    fullRecordGapCenterValue + 320156,
    fullRecordGapCenterValue + 320166,
    fullRecordGapCenterValue + 320282,
    fullRecordGapCenterValue + 320286,
    fullRecordGapCenterValue + 320402,
    fullRecordGapCenterValue + 320442,
    fullRecordGapCenterValue + 320462,
    fullRecordGapCenterValue + 320486,
    fullRecordGapCenterValue + 320588,
    fullRecordGapCenterValue + 320618,
    fullRecordGapCenterValue + 320622,
    fullRecordGapCenterValue + 320846,
    fullRecordGapCenterValue + 320906,
    fullRecordGapCenterValue + 321158,
    fullRecordGapCenterValue + 321162,
    fullRecordGapCenterValue + 321206,
    fullRecordGapCenterValue + 321242,
    fullRecordGapCenterValue + 321302,
    fullRecordGapCenterValue + 321326,
    fullRecordGapCenterValue + 321338,
    fullRecordGapCenterValue + 321506,
    fullRecordGapCenterValue + 321546,
    fullRecordGapCenterValue + 321578,
    fullRecordGapCenterValue + 321626,
    fullRecordGapCenterValue + 321722,
    fullRecordGapCenterValue + 321798,
    fullRecordGapCenterValue + 321918,
    fullRecordGapCenterValue + 321938,
    fullRecordGapCenterValue + 321942,
    fullRecordGapCenterValue + 321956,
    fullRecordGapCenterValue + 321962,
    fullRecordGapCenterValue + 322086]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00095_fermat : ∀ n ∈ fullRecordGapRow00095_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06017_not_prime : ¬(recordGapCenter + 316898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316898]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06018_not_prime : ¬(recordGapCenter + 316932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 316932]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06019_not_prime : ¬(recordGapCenter + 317166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 317166]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06020_not_prime : ¬(recordGapCenter + 317276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 317276]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06021_not_prime : ¬(recordGapCenter + 317298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 317298]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06022_not_prime : ¬(recordGapCenter + 317396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 317396]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06023_not_prime : ¬(recordGapCenter + 317406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 317406]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06024_not_prime : ¬(recordGapCenter + 317468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 317468]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06025_not_prime : ¬(recordGapCenter + 317516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 317516]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06026_not_prime : ¬(recordGapCenter + 317886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 317886]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06027_not_prime : ¬(recordGapCenter + 317972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 317972]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06028_not_prime : ¬(recordGapCenter + 318026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 318026]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06029_not_prime : ¬(recordGapCenter + 318102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 318102]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06030_not_prime : ¬(recordGapCenter + 318158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 318158]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06031_not_prime : ¬(recordGapCenter + 318398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 318398]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06032_not_prime : ¬(recordGapCenter + 318462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 318462]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06033_not_prime : ¬(recordGapCenter + 318558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 318558]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06034_not_prime : ¬(recordGapCenter + 318722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 318722]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06035_not_prime : ¬(recordGapCenter + 318788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 318788]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06036_not_prime : ¬(recordGapCenter + 318806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 318806]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06037_not_prime : ¬(recordGapCenter + 318938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 318938]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06038_not_prime : ¬(recordGapCenter + 318966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 318966]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06039_not_prime : ¬(recordGapCenter + 319028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 319028]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06040_not_prime : ¬(recordGapCenter + 319082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 319082]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06041_not_prime : ¬(recordGapCenter + 319182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 319182]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06042_not_prime : ¬(recordGapCenter + 319268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 319268]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06043_not_prime : ¬(recordGapCenter + 319386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 319386]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06044_not_prime : ¬(recordGapCenter + 319628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 319628]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06045_not_prime : ¬(recordGapCenter + 319686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 319686]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06046_not_prime : ¬(recordGapCenter + 319742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 319742]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06047_not_prime : ¬(recordGapCenter + 319916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 319916]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06048_not_prime : ¬(recordGapCenter + 319938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 319938]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06049_not_prime : ¬(recordGapCenter + 320156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 320156]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06050_not_prime : ¬(recordGapCenter + 320166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 320166]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06051_not_prime : ¬(recordGapCenter + 320282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 320282]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06052_not_prime : ¬(recordGapCenter + 320286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 320286]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06053_not_prime : ¬(recordGapCenter + 320402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 320402]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06054_not_prime : ¬(recordGapCenter + 320442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 320442]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06055_not_prime : ¬(recordGapCenter + 320462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 320462]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06056_not_prime : ¬(recordGapCenter + 320486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 320486]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06057_not_prime : ¬(recordGapCenter + 320588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 320588]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06058_not_prime : ¬(recordGapCenter + 320618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 320618]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06059_not_prime : ¬(recordGapCenter + 320622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 320622]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06060_not_prime : ¬(recordGapCenter + 320846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 320846]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06061_not_prime : ¬(recordGapCenter + 320906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 320906]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06062_not_prime : ¬(recordGapCenter + 321158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321158]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06063_not_prime : ¬(recordGapCenter + 321162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321162]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06064_not_prime : ¬(recordGapCenter + 321206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321206]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06065_not_prime : ¬(recordGapCenter + 321242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321242]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06066_not_prime : ¬(recordGapCenter + 321302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321302]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06067_not_prime : ¬(recordGapCenter + 321326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321326]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06068_not_prime : ¬(recordGapCenter + 321338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321338]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06069_not_prime : ¬(recordGapCenter + 321506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321506]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06070_not_prime : ¬(recordGapCenter + 321546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321546]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06071_not_prime : ¬(recordGapCenter + 321578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321578]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06072_not_prime : ¬(recordGapCenter + 321626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321626]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06073_not_prime : ¬(recordGapCenter + 321722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321722]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06074_not_prime : ¬(recordGapCenter + 321798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321798]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06075_not_prime : ¬(recordGapCenter + 321918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321918]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06076_not_prime : ¬(recordGapCenter + 321938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321938]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06077_not_prime : ¬(recordGapCenter + 321942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321942]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06078_not_prime : ¬(recordGapCenter + 321956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321956]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06079_not_prime : ¬(recordGapCenter + 321962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 321962]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

theorem fullRecordGapTerm06080_not_prime : ¬(recordGapCenter + 322086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 322086]
  · apply fullRecordGapRow00095_fermat
    simp [fullRecordGapRow00095_values]

end PrimeFactorUnimodality
