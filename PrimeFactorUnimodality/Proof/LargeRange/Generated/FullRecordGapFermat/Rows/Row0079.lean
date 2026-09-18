import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00079_values : List Nat :=
  [fullRecordGapCenterValue + 222542,
    fullRecordGapCenterValue + 222668,
    fullRecordGapCenterValue + 222818,
    fullRecordGapCenterValue + 222986,
    fullRecordGapCenterValue + 223052,
    fullRecordGapCenterValue + 223148,
    fullRecordGapCenterValue + 223316,
    fullRecordGapCenterValue + 223562,
    fullRecordGapCenterValue + 223742,
    fullRecordGapCenterValue + 223946,
    fullRecordGapCenterValue + 224036,
    fullRecordGapCenterValue + 224138,
    fullRecordGapCenterValue + 224156,
    fullRecordGapCenterValue + 224222,
    fullRecordGapCenterValue + 224348,
    fullRecordGapCenterValue + 224372,
    fullRecordGapCenterValue + 224492,
    fullRecordGapCenterValue + 224522,
    fullRecordGapCenterValue + 224558,
    fullRecordGapCenterValue + 224582,
    fullRecordGapCenterValue + 224828,
    fullRecordGapCenterValue + 224996,
    fullRecordGapCenterValue + 225002,
    fullRecordGapCenterValue + 225086,
    fullRecordGapCenterValue + 225326,
    fullRecordGapCenterValue + 225332,
    fullRecordGapCenterValue + 225572,
    fullRecordGapCenterValue + 225668,
    fullRecordGapCenterValue + 225818,
    fullRecordGapCenterValue + 225842,
    fullRecordGapCenterValue + 225878,
    fullRecordGapCenterValue + 225908,
    fullRecordGapCenterValue + 226076,
    fullRecordGapCenterValue + 226166,
    fullRecordGapCenterValue + 226172,
    fullRecordGapCenterValue + 226298,
    fullRecordGapCenterValue + 226346,
    fullRecordGapCenterValue + 226418,
    fullRecordGapCenterValue + 226532,
    fullRecordGapCenterValue + 226658,
    fullRecordGapCenterValue + 226718,
    fullRecordGapCenterValue + 226748,
    fullRecordGapCenterValue + 226766,
    fullRecordGapCenterValue + 227132,
    fullRecordGapCenterValue + 227462,
    fullRecordGapCenterValue + 227522,
    fullRecordGapCenterValue + 227588,
    fullRecordGapCenterValue + 227852,
    fullRecordGapCenterValue + 227972,
    fullRecordGapCenterValue + 227978,
    fullRecordGapCenterValue + 228086,
    fullRecordGapCenterValue + 228096,
    fullRecordGapCenterValue + 228146,
    fullRecordGapCenterValue + 228236,
    fullRecordGapCenterValue + 228308,
    fullRecordGapCenterValue + 228386,
    fullRecordGapCenterValue + 228398,
    fullRecordGapCenterValue + 228476,
    fullRecordGapCenterValue + 228518,
    fullRecordGapCenterValue + 228638,
    fullRecordGapCenterValue + 228690,
    fullRecordGapCenterValue + 228692,
    fullRecordGapCenterValue + 228716,
    fullRecordGapCenterValue + 228902]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00079_fermat : ∀ n ∈ fullRecordGapRow00079_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04993_not_prime : ¬(recordGapCenter + 222542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 222542]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm04994_not_prime : ¬(recordGapCenter + 222668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 222668]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm04995_not_prime : ¬(recordGapCenter + 222818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 222818]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm04996_not_prime : ¬(recordGapCenter + 222986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 222986]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm04997_not_prime : ¬(recordGapCenter + 223052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 223052]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm04998_not_prime : ¬(recordGapCenter + 223148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 223148]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm04999_not_prime : ¬(recordGapCenter + 223316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 223316]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05000_not_prime : ¬(recordGapCenter + 223562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 223562]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05001_not_prime : ¬(recordGapCenter + 223742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 223742]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05002_not_prime : ¬(recordGapCenter + 223946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 223946]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05003_not_prime : ¬(recordGapCenter + 224036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 224036]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05004_not_prime : ¬(recordGapCenter + 224138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 224138]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05005_not_prime : ¬(recordGapCenter + 224156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 224156]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05006_not_prime : ¬(recordGapCenter + 224222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 224222]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05007_not_prime : ¬(recordGapCenter + 224348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 224348]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05008_not_prime : ¬(recordGapCenter + 224372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 224372]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05009_not_prime : ¬(recordGapCenter + 224492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 224492]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05010_not_prime : ¬(recordGapCenter + 224522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 224522]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05011_not_prime : ¬(recordGapCenter + 224558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 224558]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05012_not_prime : ¬(recordGapCenter + 224582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 224582]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05013_not_prime : ¬(recordGapCenter + 224828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 224828]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05014_not_prime : ¬(recordGapCenter + 224996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 224996]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05015_not_prime : ¬(recordGapCenter + 225002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 225002]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05016_not_prime : ¬(recordGapCenter + 225086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 225086]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05017_not_prime : ¬(recordGapCenter + 225326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 225326]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05018_not_prime : ¬(recordGapCenter + 225332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 225332]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05019_not_prime : ¬(recordGapCenter + 225572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 225572]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05020_not_prime : ¬(recordGapCenter + 225668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 225668]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05021_not_prime : ¬(recordGapCenter + 225818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 225818]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05022_not_prime : ¬(recordGapCenter + 225842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 225842]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05023_not_prime : ¬(recordGapCenter + 225878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 225878]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05024_not_prime : ¬(recordGapCenter + 225908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 225908]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05025_not_prime : ¬(recordGapCenter + 226076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 226076]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05026_not_prime : ¬(recordGapCenter + 226166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 226166]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05027_not_prime : ¬(recordGapCenter + 226172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 226172]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05028_not_prime : ¬(recordGapCenter + 226298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 226298]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05029_not_prime : ¬(recordGapCenter + 226346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 226346]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05030_not_prime : ¬(recordGapCenter + 226418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 226418]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05031_not_prime : ¬(recordGapCenter + 226532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 226532]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05032_not_prime : ¬(recordGapCenter + 226658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 226658]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05033_not_prime : ¬(recordGapCenter + 226718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 226718]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05034_not_prime : ¬(recordGapCenter + 226748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 226748]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05035_not_prime : ¬(recordGapCenter + 226766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 226766]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05036_not_prime : ¬(recordGapCenter + 227132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 227132]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05037_not_prime : ¬(recordGapCenter + 227462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 227462]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05038_not_prime : ¬(recordGapCenter + 227522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 227522]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05039_not_prime : ¬(recordGapCenter + 227588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 227588]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05040_not_prime : ¬(recordGapCenter + 227852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 227852]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05041_not_prime : ¬(recordGapCenter + 227972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 227972]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05042_not_prime : ¬(recordGapCenter + 227978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 227978]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05043_not_prime : ¬(recordGapCenter + 228086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 228086]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05044_not_prime : ¬(recordGapCenter + 228096).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 228096]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05045_not_prime : ¬(recordGapCenter + 228146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 228146]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05046_not_prime : ¬(recordGapCenter + 228236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 228236]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05047_not_prime : ¬(recordGapCenter + 228308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 228308]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05048_not_prime : ¬(recordGapCenter + 228386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 228386]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05049_not_prime : ¬(recordGapCenter + 228398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 228398]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05050_not_prime : ¬(recordGapCenter + 228476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 228476]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05051_not_prime : ¬(recordGapCenter + 228518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 228518]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05052_not_prime : ¬(recordGapCenter + 228638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 228638]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05053_not_prime : ¬(recordGapCenter + 228690).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 228690]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05054_not_prime : ¬(recordGapCenter + 228692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 228692]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05055_not_prime : ¬(recordGapCenter + 228716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 228716]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

theorem fullRecordGapTerm05056_not_prime : ¬(recordGapCenter + 228902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 228902]
  · apply fullRecordGapRow00079_fermat
    simp [fullRecordGapRow00079_values]

end PrimeFactorUnimodality
