import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00022_values : List Nat :=
  [fullRecordGapCenterValue - 348438,
    fullRecordGapCenterValue - 348298,
    fullRecordGapCenterValue - 348294,
    fullRecordGapCenterValue - 348148,
    fullRecordGapCenterValue - 348078,
    fullRecordGapCenterValue - 348052,
    fullRecordGapCenterValue - 347938,
    fullRecordGapCenterValue - 347848,
    fullRecordGapCenterValue - 347818,
    fullRecordGapCenterValue - 347734,
    fullRecordGapCenterValue - 347722,
    fullRecordGapCenterValue - 347682,
    fullRecordGapCenterValue - 347554,
    fullRecordGapCenterValue - 347482,
    fullRecordGapCenterValue - 347458,
    fullRecordGapCenterValue - 347394,
    fullRecordGapCenterValue - 347224,
    fullRecordGapCenterValue - 347128,
    fullRecordGapCenterValue - 347034,
    fullRecordGapCenterValue - 346972,
    fullRecordGapCenterValue - 346722,
    fullRecordGapCenterValue - 346714,
    fullRecordGapCenterValue - 346638,
    fullRecordGapCenterValue - 346618,
    fullRecordGapCenterValue - 346552,
    fullRecordGapCenterValue - 346348,
    fullRecordGapCenterValue - 346282,
    fullRecordGapCenterValue - 346168,
    fullRecordGapCenterValue - 346162,
    fullRecordGapCenterValue - 346078,
    fullRecordGapCenterValue - 346002,
    fullRecordGapCenterValue - 345964,
    fullRecordGapCenterValue - 345784,
    fullRecordGapCenterValue - 345754,
    fullRecordGapCenterValue - 345744,
    fullRecordGapCenterValue - 345742,
    fullRecordGapCenterValue - 345718,
    fullRecordGapCenterValue - 345658,
    fullRecordGapCenterValue - 345652,
    fullRecordGapCenterValue - 345600,
    fullRecordGapCenterValue - 345354,
    fullRecordGapCenterValue - 345342,
    fullRecordGapCenterValue - 345292,
    fullRecordGapCenterValue - 345244,
    fullRecordGapCenterValue - 345208,
    fullRecordGapCenterValue - 345174,
    fullRecordGapCenterValue - 345172,
    fullRecordGapCenterValue - 345064,
    fullRecordGapCenterValue - 345034,
    fullRecordGapCenterValue - 345018,
    fullRecordGapCenterValue - 344958,
    fullRecordGapCenterValue - 344922,
    fullRecordGapCenterValue - 344742,
    fullRecordGapCenterValue - 344662,
    fullRecordGapCenterValue - 344644,
    fullRecordGapCenterValue - 344614,
    fullRecordGapCenterValue - 344572,
    fullRecordGapCenterValue - 344518,
    fullRecordGapCenterValue - 344452,
    fullRecordGapCenterValue - 344334,
    fullRecordGapCenterValue - 344332,
    fullRecordGapCenterValue - 344308,
    fullRecordGapCenterValue - 344298,
    fullRecordGapCenterValue - 344064]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00022_fermat : ∀ n ∈ fullRecordGapRow00022_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01345_not_prime : ¬(recordGapCenter - 348438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348438]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01346_not_prime : ¬(recordGapCenter - 348298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348298]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01347_not_prime : ¬(recordGapCenter - 348294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348294]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01348_not_prime : ¬(recordGapCenter - 348148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348148]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01349_not_prime : ¬(recordGapCenter - 348078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348078]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01350_not_prime : ¬(recordGapCenter - 348052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 348052]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01351_not_prime : ¬(recordGapCenter - 347938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347938]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01352_not_prime : ¬(recordGapCenter - 347848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347848]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01353_not_prime : ¬(recordGapCenter - 347818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347818]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01354_not_prime : ¬(recordGapCenter - 347734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347734]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01355_not_prime : ¬(recordGapCenter - 347722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347722]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01356_not_prime : ¬(recordGapCenter - 347682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347682]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01357_not_prime : ¬(recordGapCenter - 347554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347554]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01358_not_prime : ¬(recordGapCenter - 347482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347482]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01359_not_prime : ¬(recordGapCenter - 347458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347458]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01360_not_prime : ¬(recordGapCenter - 347394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347394]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01361_not_prime : ¬(recordGapCenter - 347224).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347224]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01362_not_prime : ¬(recordGapCenter - 347128).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347128]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01363_not_prime : ¬(recordGapCenter - 347034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 347034]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01364_not_prime : ¬(recordGapCenter - 346972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346972]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01365_not_prime : ¬(recordGapCenter - 346722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346722]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01366_not_prime : ¬(recordGapCenter - 346714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346714]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01367_not_prime : ¬(recordGapCenter - 346638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346638]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01368_not_prime : ¬(recordGapCenter - 346618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346618]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01369_not_prime : ¬(recordGapCenter - 346552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346552]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01370_not_prime : ¬(recordGapCenter - 346348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346348]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01371_not_prime : ¬(recordGapCenter - 346282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346282]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01372_not_prime : ¬(recordGapCenter - 346168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346168]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01373_not_prime : ¬(recordGapCenter - 346162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346162]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01374_not_prime : ¬(recordGapCenter - 346078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346078]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01375_not_prime : ¬(recordGapCenter - 346002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 346002]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01376_not_prime : ¬(recordGapCenter - 345964).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345964]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01377_not_prime : ¬(recordGapCenter - 345784).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345784]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01378_not_prime : ¬(recordGapCenter - 345754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345754]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01379_not_prime : ¬(recordGapCenter - 345744).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345744]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01380_not_prime : ¬(recordGapCenter - 345742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345742]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01381_not_prime : ¬(recordGapCenter - 345718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345718]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01382_not_prime : ¬(recordGapCenter - 345658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345658]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01383_not_prime : ¬(recordGapCenter - 345652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345652]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01384_not_prime : ¬(recordGapCenter - 345600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345600]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01385_not_prime : ¬(recordGapCenter - 345354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345354]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01386_not_prime : ¬(recordGapCenter - 345342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345342]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01387_not_prime : ¬(recordGapCenter - 345292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345292]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01388_not_prime : ¬(recordGapCenter - 345244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345244]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01389_not_prime : ¬(recordGapCenter - 345208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345208]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01390_not_prime : ¬(recordGapCenter - 345174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345174]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01391_not_prime : ¬(recordGapCenter - 345172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345172]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01392_not_prime : ¬(recordGapCenter - 345064).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345064]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01393_not_prime : ¬(recordGapCenter - 345034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345034]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01394_not_prime : ¬(recordGapCenter - 345018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 345018]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01395_not_prime : ¬(recordGapCenter - 344958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344958]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01396_not_prime : ¬(recordGapCenter - 344922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344922]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01397_not_prime : ¬(recordGapCenter - 344742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344742]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01398_not_prime : ¬(recordGapCenter - 344662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344662]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01399_not_prime : ¬(recordGapCenter - 344644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344644]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01400_not_prime : ¬(recordGapCenter - 344614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344614]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01401_not_prime : ¬(recordGapCenter - 344572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344572]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01402_not_prime : ¬(recordGapCenter - 344518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344518]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01403_not_prime : ¬(recordGapCenter - 344452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344452]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01404_not_prime : ¬(recordGapCenter - 344334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344334]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01405_not_prime : ¬(recordGapCenter - 344332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344332]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01406_not_prime : ¬(recordGapCenter - 344308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344308]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01407_not_prime : ¬(recordGapCenter - 344298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344298]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

theorem fullRecordGapTerm01408_not_prime : ¬(recordGapCenter - 344064).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 344064]
  · apply fullRecordGapRow00022_fermat
    simp [fullRecordGapRow00022_values]

end PrimeFactorUnimodality
