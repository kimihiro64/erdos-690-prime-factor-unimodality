import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00031_values : List Nat :=
  [fullRecordGapCenterValue - 299434,
    fullRecordGapCenterValue - 299428,
    fullRecordGapCenterValue - 299308,
    fullRecordGapCenterValue - 299058,
    fullRecordGapCenterValue - 298882,
    fullRecordGapCenterValue - 298834,
    fullRecordGapCenterValue - 298798,
    fullRecordGapCenterValue - 298762,
    fullRecordGapCenterValue - 298734,
    fullRecordGapCenterValue - 298618,
    fullRecordGapCenterValue - 298542,
    fullRecordGapCenterValue - 298492,
    fullRecordGapCenterValue - 298482,
    fullRecordGapCenterValue - 298318,
    fullRecordGapCenterValue - 298198,
    fullRecordGapCenterValue - 298084,
    fullRecordGapCenterValue - 297978,
    fullRecordGapCenterValue - 297922,
    fullRecordGapCenterValue - 297834,
    fullRecordGapCenterValue - 297658,
    fullRecordGapCenterValue - 297652,
    fullRecordGapCenterValue - 297618,
    fullRecordGapCenterValue - 297582,
    fullRecordGapCenterValue - 297442,
    fullRecordGapCenterValue - 297412,
    fullRecordGapCenterValue - 297294,
    fullRecordGapCenterValue - 297292,
    fullRecordGapCenterValue - 297282,
    fullRecordGapCenterValue - 297148,
    fullRecordGapCenterValue - 297138,
    fullRecordGapCenterValue - 297034,
    fullRecordGapCenterValue - 296778,
    fullRecordGapCenterValue - 296602,
    fullRecordGapCenterValue - 296524,
    fullRecordGapCenterValue - 296284,
    fullRecordGapCenterValue - 296214,
    fullRecordGapCenterValue - 296202,
    fullRecordGapCenterValue - 296158,
    fullRecordGapCenterValue - 295998,
    fullRecordGapCenterValue - 295680,
    fullRecordGapCenterValue - 295654,
    fullRecordGapCenterValue - 295588,
    fullRecordGapCenterValue - 295558,
    fullRecordGapCenterValue - 295468,
    fullRecordGapCenterValue - 295294,
    fullRecordGapCenterValue - 295258,
    fullRecordGapCenterValue - 295242,
    fullRecordGapCenterValue - 295234,
    fullRecordGapCenterValue - 295194,
    fullRecordGapCenterValue - 295132,
    fullRecordGapCenterValue - 295084,
    fullRecordGapCenterValue - 294912,
    fullRecordGapCenterValue - 294772,
    fullRecordGapCenterValue - 294754,
    fullRecordGapCenterValue - 294702,
    fullRecordGapCenterValue - 294682,
    fullRecordGapCenterValue - 294618,
    fullRecordGapCenterValue - 294394,
    fullRecordGapCenterValue - 294222,
    fullRecordGapCenterValue - 294214,
    fullRecordGapCenterValue - 294114,
    fullRecordGapCenterValue - 294058,
    fullRecordGapCenterValue - 294000,
    fullRecordGapCenterValue - 293932]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00031_fermat : ∀ n ∈ fullRecordGapRow00031_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01921_not_prime : ¬(recordGapCenter - 299434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299434]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01922_not_prime : ¬(recordGapCenter - 299428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299428]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01923_not_prime : ¬(recordGapCenter - 299308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299308]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01924_not_prime : ¬(recordGapCenter - 299058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 299058]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01925_not_prime : ¬(recordGapCenter - 298882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298882]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01926_not_prime : ¬(recordGapCenter - 298834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298834]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01927_not_prime : ¬(recordGapCenter - 298798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298798]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01928_not_prime : ¬(recordGapCenter - 298762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298762]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01929_not_prime : ¬(recordGapCenter - 298734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298734]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01930_not_prime : ¬(recordGapCenter - 298618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298618]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01931_not_prime : ¬(recordGapCenter - 298542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298542]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01932_not_prime : ¬(recordGapCenter - 298492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298492]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01933_not_prime : ¬(recordGapCenter - 298482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298482]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01934_not_prime : ¬(recordGapCenter - 298318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298318]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01935_not_prime : ¬(recordGapCenter - 298198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298198]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01936_not_prime : ¬(recordGapCenter - 298084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 298084]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01937_not_prime : ¬(recordGapCenter - 297978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297978]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01938_not_prime : ¬(recordGapCenter - 297922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297922]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01939_not_prime : ¬(recordGapCenter - 297834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297834]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01940_not_prime : ¬(recordGapCenter - 297658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297658]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01941_not_prime : ¬(recordGapCenter - 297652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297652]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01942_not_prime : ¬(recordGapCenter - 297618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297618]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01943_not_prime : ¬(recordGapCenter - 297582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297582]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01944_not_prime : ¬(recordGapCenter - 297442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297442]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01945_not_prime : ¬(recordGapCenter - 297412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297412]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01946_not_prime : ¬(recordGapCenter - 297294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297294]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01947_not_prime : ¬(recordGapCenter - 297292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297292]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01948_not_prime : ¬(recordGapCenter - 297282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297282]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01949_not_prime : ¬(recordGapCenter - 297148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297148]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01950_not_prime : ¬(recordGapCenter - 297138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297138]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01951_not_prime : ¬(recordGapCenter - 297034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 297034]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01952_not_prime : ¬(recordGapCenter - 296778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 296778]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01953_not_prime : ¬(recordGapCenter - 296602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 296602]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01954_not_prime : ¬(recordGapCenter - 296524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 296524]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01955_not_prime : ¬(recordGapCenter - 296284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 296284]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01956_not_prime : ¬(recordGapCenter - 296214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 296214]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01957_not_prime : ¬(recordGapCenter - 296202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 296202]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01958_not_prime : ¬(recordGapCenter - 296158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 296158]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01959_not_prime : ¬(recordGapCenter - 295998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295998]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01960_not_prime : ¬(recordGapCenter - 295680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295680]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01961_not_prime : ¬(recordGapCenter - 295654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295654]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01962_not_prime : ¬(recordGapCenter - 295588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295588]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01963_not_prime : ¬(recordGapCenter - 295558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295558]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01964_not_prime : ¬(recordGapCenter - 295468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295468]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01965_not_prime : ¬(recordGapCenter - 295294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295294]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01966_not_prime : ¬(recordGapCenter - 295258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295258]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01967_not_prime : ¬(recordGapCenter - 295242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295242]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01968_not_prime : ¬(recordGapCenter - 295234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295234]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01969_not_prime : ¬(recordGapCenter - 295194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295194]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01970_not_prime : ¬(recordGapCenter - 295132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295132]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01971_not_prime : ¬(recordGapCenter - 295084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 295084]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01972_not_prime : ¬(recordGapCenter - 294912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294912]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01973_not_prime : ¬(recordGapCenter - 294772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294772]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01974_not_prime : ¬(recordGapCenter - 294754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294754]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01975_not_prime : ¬(recordGapCenter - 294702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294702]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01976_not_prime : ¬(recordGapCenter - 294682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294682]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01977_not_prime : ¬(recordGapCenter - 294618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294618]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01978_not_prime : ¬(recordGapCenter - 294394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294394]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01979_not_prime : ¬(recordGapCenter - 294222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294222]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01980_not_prime : ¬(recordGapCenter - 294214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294214]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01981_not_prime : ¬(recordGapCenter - 294114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294114]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01982_not_prime : ¬(recordGapCenter - 294058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294058]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01983_not_prime : ¬(recordGapCenter - 294000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 294000]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

theorem fullRecordGapTerm01984_not_prime : ¬(recordGapCenter - 293932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293932]
  · apply fullRecordGapRow00031_fermat
    simp [fullRecordGapRow00031_values]

end PrimeFactorUnimodality
