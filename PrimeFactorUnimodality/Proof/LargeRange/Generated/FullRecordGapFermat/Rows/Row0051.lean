import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00051_values : List Nat :=
  [fullRecordGapCenterValue - 151594,
    fullRecordGapCenterValue - 151414,
    fullRecordGapCenterValue - 151282,
    fullRecordGapCenterValue - 151258,
    fullRecordGapCenterValue - 151234,
    fullRecordGapCenterValue - 151200,
    fullRecordGapCenterValue - 150958,
    fullRecordGapCenterValue - 150694,
    fullRecordGapCenterValue - 150538,
    fullRecordGapCenterValue - 150034,
    fullRecordGapCenterValue - 149398,
    fullRecordGapCenterValue - 149134,
    fullRecordGapCenterValue - 149062,
    fullRecordGapCenterValue - 148942,
    fullRecordGapCenterValue - 148714,
    fullRecordGapCenterValue - 148462,
    fullRecordGapCenterValue - 148354,
    fullRecordGapCenterValue - 148102,
    fullRecordGapCenterValue - 148054,
    fullRecordGapCenterValue - 147840,
    fullRecordGapCenterValue - 147214,
    fullRecordGapCenterValue - 147094,
    fullRecordGapCenterValue - 146758,
    fullRecordGapCenterValue - 146662,
    fullRecordGapCenterValue - 146410,
    fullRecordGapCenterValue - 146362,
    fullRecordGapCenterValue - 146158,
    fullRecordGapCenterValue - 146038,
    fullRecordGapCenterValue - 145954,
    fullRecordGapCenterValue - 145800,
    fullRecordGapCenterValue - 145738,
    fullRecordGapCenterValue - 145438,
    fullRecordGapCenterValue - 145414,
    fullRecordGapCenterValue - 145102,
    fullRecordGapCenterValue - 144934,
    fullRecordGapCenterValue - 144862,
    fullRecordGapCenterValue - 144682,
    fullRecordGapCenterValue - 144574,
    fullRecordGapCenterValue - 144322,
    fullRecordGapCenterValue - 144178,
    fullRecordGapCenterValue - 144154,
    fullRecordGapCenterValue - 143974,
    fullRecordGapCenterValue - 143748,
    fullRecordGapCenterValue - 143722,
    fullRecordGapCenterValue - 143698,
    fullRecordGapCenterValue - 143614,
    fullRecordGapCenterValue - 143398,
    fullRecordGapCenterValue - 143098,
    fullRecordGapCenterValue - 142884,
    fullRecordGapCenterValue - 142858,
    fullRecordGapCenterValue - 142678,
    fullRecordGapCenterValue - 142342,
    fullRecordGapCenterValue - 142294,
    fullRecordGapCenterValue - 142162,
    fullRecordGapCenterValue - 142138,
    fullRecordGapCenterValue - 141874,
    fullRecordGapCenterValue - 141682,
    fullRecordGapCenterValue - 141238,
    fullRecordGapCenterValue - 140962,
    fullRecordGapCenterValue - 140878,
    fullRecordGapCenterValue - 140362,
    fullRecordGapCenterValue - 140242,
    fullRecordGapCenterValue - 140158,
    fullRecordGapCenterValue - 140038]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00051_fermat : ∀ n ∈ fullRecordGapRow00051_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03201_not_prime : ¬(recordGapCenter - 151594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 151594]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03202_not_prime : ¬(recordGapCenter - 151414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 151414]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03203_not_prime : ¬(recordGapCenter - 151282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 151282]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03204_not_prime : ¬(recordGapCenter - 151258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 151258]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03205_not_prime : ¬(recordGapCenter - 151234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 151234]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03206_not_prime : ¬(recordGapCenter - 151200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 151200]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03207_not_prime : ¬(recordGapCenter - 150958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 150958]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03208_not_prime : ¬(recordGapCenter - 150694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 150694]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03209_not_prime : ¬(recordGapCenter - 150538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 150538]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03210_not_prime : ¬(recordGapCenter - 150034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 150034]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03211_not_prime : ¬(recordGapCenter - 149398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 149398]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03212_not_prime : ¬(recordGapCenter - 149134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 149134]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03213_not_prime : ¬(recordGapCenter - 149062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 149062]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03214_not_prime : ¬(recordGapCenter - 148942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 148942]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03215_not_prime : ¬(recordGapCenter - 148714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 148714]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03216_not_prime : ¬(recordGapCenter - 148462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 148462]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03217_not_prime : ¬(recordGapCenter - 148354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 148354]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03218_not_prime : ¬(recordGapCenter - 148102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 148102]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03219_not_prime : ¬(recordGapCenter - 148054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 148054]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03220_not_prime : ¬(recordGapCenter - 147840).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 147840]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03221_not_prime : ¬(recordGapCenter - 147214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 147214]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03222_not_prime : ¬(recordGapCenter - 147094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 147094]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03223_not_prime : ¬(recordGapCenter - 146758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 146758]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03224_not_prime : ¬(recordGapCenter - 146662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 146662]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03225_not_prime : ¬(recordGapCenter - 146410).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 146410]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03226_not_prime : ¬(recordGapCenter - 146362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 146362]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03227_not_prime : ¬(recordGapCenter - 146158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 146158]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03228_not_prime : ¬(recordGapCenter - 146038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 146038]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03229_not_prime : ¬(recordGapCenter - 145954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 145954]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03230_not_prime : ¬(recordGapCenter - 145800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 145800]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03231_not_prime : ¬(recordGapCenter - 145738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 145738]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03232_not_prime : ¬(recordGapCenter - 145438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 145438]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03233_not_prime : ¬(recordGapCenter - 145414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 145414]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03234_not_prime : ¬(recordGapCenter - 145102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 145102]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03235_not_prime : ¬(recordGapCenter - 144934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 144934]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03236_not_prime : ¬(recordGapCenter - 144862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 144862]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03237_not_prime : ¬(recordGapCenter - 144682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 144682]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03238_not_prime : ¬(recordGapCenter - 144574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 144574]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03239_not_prime : ¬(recordGapCenter - 144322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 144322]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03240_not_prime : ¬(recordGapCenter - 144178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 144178]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03241_not_prime : ¬(recordGapCenter - 144154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 144154]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03242_not_prime : ¬(recordGapCenter - 143974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 143974]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03243_not_prime : ¬(recordGapCenter - 143748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 143748]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03244_not_prime : ¬(recordGapCenter - 143722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 143722]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03245_not_prime : ¬(recordGapCenter - 143698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 143698]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03246_not_prime : ¬(recordGapCenter - 143614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 143614]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03247_not_prime : ¬(recordGapCenter - 143398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 143398]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03248_not_prime : ¬(recordGapCenter - 143098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 143098]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03249_not_prime : ¬(recordGapCenter - 142884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 142884]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03250_not_prime : ¬(recordGapCenter - 142858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 142858]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03251_not_prime : ¬(recordGapCenter - 142678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 142678]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03252_not_prime : ¬(recordGapCenter - 142342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 142342]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03253_not_prime : ¬(recordGapCenter - 142294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 142294]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03254_not_prime : ¬(recordGapCenter - 142162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 142162]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03255_not_prime : ¬(recordGapCenter - 142138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 142138]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03256_not_prime : ¬(recordGapCenter - 141874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 141874]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03257_not_prime : ¬(recordGapCenter - 141682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 141682]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03258_not_prime : ¬(recordGapCenter - 141238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 141238]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03259_not_prime : ¬(recordGapCenter - 140962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 140962]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03260_not_prime : ¬(recordGapCenter - 140878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 140878]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03261_not_prime : ¬(recordGapCenter - 140362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 140362]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03262_not_prime : ¬(recordGapCenter - 140242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 140242]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03263_not_prime : ¬(recordGapCenter - 140158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 140158]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

theorem fullRecordGapTerm03264_not_prime : ¬(recordGapCenter - 140038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 140038]
  · apply fullRecordGapRow00051_fermat
    simp [fullRecordGapRow00051_values]

end PrimeFactorUnimodality
