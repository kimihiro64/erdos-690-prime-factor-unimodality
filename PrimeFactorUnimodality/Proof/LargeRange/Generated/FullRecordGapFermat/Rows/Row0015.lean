import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00015_values : List Nat :=
  [fullRecordGapCenterValue - 384160,
    fullRecordGapCenterValue - 384094,
    fullRecordGapCenterValue - 384004,
    fullRecordGapCenterValue - 383998,
    fullRecordGapCenterValue - 383938,
    fullRecordGapCenterValue - 383862,
    fullRecordGapCenterValue - 383788,
    fullRecordGapCenterValue - 383752,
    fullRecordGapCenterValue - 383722,
    fullRecordGapCenterValue - 383694,
    fullRecordGapCenterValue - 383668,
    fullRecordGapCenterValue - 383512,
    fullRecordGapCenterValue - 383494,
    fullRecordGapCenterValue - 383434,
    fullRecordGapCenterValue - 383242,
    fullRecordGapCenterValue - 383224,
    fullRecordGapCenterValue - 383164,
    fullRecordGapCenterValue - 383158,
    fullRecordGapCenterValue - 383122,
    fullRecordGapCenterValue - 383074,
    fullRecordGapCenterValue - 383038,
    fullRecordGapCenterValue - 383014,
    fullRecordGapCenterValue - 382938,
    fullRecordGapCenterValue - 382918,
    fullRecordGapCenterValue - 382882,
    fullRecordGapCenterValue - 382854,
    fullRecordGapCenterValue - 382828,
    fullRecordGapCenterValue - 382818,
    fullRecordGapCenterValue - 382758,
    fullRecordGapCenterValue - 382638,
    fullRecordGapCenterValue - 382498,
    fullRecordGapCenterValue - 382314,
    fullRecordGapCenterValue - 382218,
    fullRecordGapCenterValue - 382198,
    fullRecordGapCenterValue - 382042,
    fullRecordGapCenterValue - 381958,
    fullRecordGapCenterValue - 381954,
    fullRecordGapCenterValue - 381882,
    fullRecordGapCenterValue - 381778,
    fullRecordGapCenterValue - 381772,
    fullRecordGapCenterValue - 381742,
    fullRecordGapCenterValue - 381688,
    fullRecordGapCenterValue - 381642,
    fullRecordGapCenterValue - 381622,
    fullRecordGapCenterValue - 381574,
    fullRecordGapCenterValue - 381538,
    fullRecordGapCenterValue - 381534,
    fullRecordGapCenterValue - 381268,
    fullRecordGapCenterValue - 381162,
    fullRecordGapCenterValue - 381112,
    fullRecordGapCenterValue - 381024,
    fullRecordGapCenterValue - 380838,
    fullRecordGapCenterValue - 380818,
    fullRecordGapCenterValue - 380572,
    fullRecordGapCenterValue - 380524,
    fullRecordGapCenterValue - 380454,
    fullRecordGapCenterValue - 380382,
    fullRecordGapCenterValue - 380344,
    fullRecordGapCenterValue - 380334,
    fullRecordGapCenterValue - 380284,
    fullRecordGapCenterValue - 380242,
    fullRecordGapCenterValue - 380118,
    fullRecordGapCenterValue - 380022,
    fullRecordGapCenterValue - 379978]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00015_fermat : ∀ n ∈ fullRecordGapRow00015_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00897_not_prime : ¬(recordGapCenter - 384160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384160]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00898_not_prime : ¬(recordGapCenter - 384094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384094]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00899_not_prime : ¬(recordGapCenter - 384004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 384004]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00900_not_prime : ¬(recordGapCenter - 383998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383998]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00901_not_prime : ¬(recordGapCenter - 383938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383938]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00902_not_prime : ¬(recordGapCenter - 383862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383862]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00903_not_prime : ¬(recordGapCenter - 383788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383788]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00904_not_prime : ¬(recordGapCenter - 383752).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383752]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00905_not_prime : ¬(recordGapCenter - 383722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383722]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00906_not_prime : ¬(recordGapCenter - 383694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383694]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00907_not_prime : ¬(recordGapCenter - 383668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383668]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00908_not_prime : ¬(recordGapCenter - 383512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383512]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00909_not_prime : ¬(recordGapCenter - 383494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383494]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00910_not_prime : ¬(recordGapCenter - 383434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383434]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00911_not_prime : ¬(recordGapCenter - 383242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383242]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00912_not_prime : ¬(recordGapCenter - 383224).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383224]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00913_not_prime : ¬(recordGapCenter - 383164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383164]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00914_not_prime : ¬(recordGapCenter - 383158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383158]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00915_not_prime : ¬(recordGapCenter - 383122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383122]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00916_not_prime : ¬(recordGapCenter - 383074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383074]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00917_not_prime : ¬(recordGapCenter - 383038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383038]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00918_not_prime : ¬(recordGapCenter - 383014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 383014]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00919_not_prime : ¬(recordGapCenter - 382938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382938]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00920_not_prime : ¬(recordGapCenter - 382918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382918]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00921_not_prime : ¬(recordGapCenter - 382882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382882]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00922_not_prime : ¬(recordGapCenter - 382854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382854]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00923_not_prime : ¬(recordGapCenter - 382828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382828]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00924_not_prime : ¬(recordGapCenter - 382818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382818]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00925_not_prime : ¬(recordGapCenter - 382758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382758]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00926_not_prime : ¬(recordGapCenter - 382638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382638]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00927_not_prime : ¬(recordGapCenter - 382498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382498]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00928_not_prime : ¬(recordGapCenter - 382314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382314]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00929_not_prime : ¬(recordGapCenter - 382218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382218]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00930_not_prime : ¬(recordGapCenter - 382198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382198]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00931_not_prime : ¬(recordGapCenter - 382042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 382042]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00932_not_prime : ¬(recordGapCenter - 381958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381958]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00933_not_prime : ¬(recordGapCenter - 381954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381954]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00934_not_prime : ¬(recordGapCenter - 381882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381882]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00935_not_prime : ¬(recordGapCenter - 381778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381778]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00936_not_prime : ¬(recordGapCenter - 381772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381772]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00937_not_prime : ¬(recordGapCenter - 381742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381742]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00938_not_prime : ¬(recordGapCenter - 381688).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381688]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00939_not_prime : ¬(recordGapCenter - 381642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381642]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00940_not_prime : ¬(recordGapCenter - 381622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381622]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00941_not_prime : ¬(recordGapCenter - 381574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381574]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00942_not_prime : ¬(recordGapCenter - 381538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381538]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00943_not_prime : ¬(recordGapCenter - 381534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381534]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00944_not_prime : ¬(recordGapCenter - 381268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381268]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00945_not_prime : ¬(recordGapCenter - 381162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381162]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00946_not_prime : ¬(recordGapCenter - 381112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381112]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00947_not_prime : ¬(recordGapCenter - 381024).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 381024]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00948_not_prime : ¬(recordGapCenter - 380838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380838]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00949_not_prime : ¬(recordGapCenter - 380818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380818]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00950_not_prime : ¬(recordGapCenter - 380572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380572]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00951_not_prime : ¬(recordGapCenter - 380524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380524]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00952_not_prime : ¬(recordGapCenter - 380454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380454]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00953_not_prime : ¬(recordGapCenter - 380382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380382]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00954_not_prime : ¬(recordGapCenter - 380344).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380344]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00955_not_prime : ¬(recordGapCenter - 380334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380334]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00956_not_prime : ¬(recordGapCenter - 380284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380284]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00957_not_prime : ¬(recordGapCenter - 380242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380242]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00958_not_prime : ¬(recordGapCenter - 380118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380118]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00959_not_prime : ¬(recordGapCenter - 380022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 380022]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

theorem fullRecordGapTerm00960_not_prime : ¬(recordGapCenter - 379978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 379978]
  · apply fullRecordGapRow00015_fermat
    simp [fullRecordGapRow00015_values]

end PrimeFactorUnimodality
