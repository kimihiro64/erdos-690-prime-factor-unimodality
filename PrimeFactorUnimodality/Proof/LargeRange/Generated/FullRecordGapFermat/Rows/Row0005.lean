import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00005_values : List Nat :=
  [fullRecordGapCenterValue - 435600,
    fullRecordGapCenterValue - 435354,
    fullRecordGapCenterValue - 435322,
    fullRecordGapCenterValue - 435304,
    fullRecordGapCenterValue - 435154,
    fullRecordGapCenterValue - 435118,
    fullRecordGapCenterValue - 434998,
    fullRecordGapCenterValue - 434982,
    fullRecordGapCenterValue - 434958,
    fullRecordGapCenterValue - 434914,
    fullRecordGapCenterValue - 434802,
    fullRecordGapCenterValue - 434734,
    fullRecordGapCenterValue - 434572,
    fullRecordGapCenterValue - 434524,
    fullRecordGapCenterValue - 434458,
    fullRecordGapCenterValue - 434410,
    fullRecordGapCenterValue - 434338,
    fullRecordGapCenterValue - 434314,
    fullRecordGapCenterValue - 434298,
    fullRecordGapCenterValue - 434242,
    fullRecordGapCenterValue - 434202,
    fullRecordGapCenterValue - 434164,
    fullRecordGapCenterValue - 434002,
    fullRecordGapCenterValue - 433990,
    fullRecordGapCenterValue - 433894,
    fullRecordGapCenterValue - 433878,
    fullRecordGapCenterValue - 433702,
    fullRecordGapCenterValue - 433684,
    fullRecordGapCenterValue - 433614,
    fullRecordGapCenterValue - 433372,
    fullRecordGapCenterValue - 433282,
    fullRecordGapCenterValue - 433138,
    fullRecordGapCenterValue - 433018,
    fullRecordGapCenterValue - 433002,
    fullRecordGapCenterValue - 432988,
    fullRecordGapCenterValue - 432910,
    fullRecordGapCenterValue - 432868,
    fullRecordGapCenterValue - 432862,
    fullRecordGapCenterValue - 432844,
    fullRecordGapCenterValue - 432802,
    fullRecordGapCenterValue - 432742,
    fullRecordGapCenterValue - 432472,
    fullRecordGapCenterValue - 432462,
    fullRecordGapCenterValue - 432358,
    fullRecordGapCenterValue - 432318,
    fullRecordGapCenterValue - 432070,
    fullRecordGapCenterValue - 432010,
    fullRecordGapCenterValue - 432000,
    fullRecordGapCenterValue - 431962,
    fullRecordGapCenterValue - 431944,
    fullRecordGapCenterValue - 431898,
    fullRecordGapCenterValue - 431890,
    fullRecordGapCenterValue - 431778,
    fullRecordGapCenterValue - 431764,
    fullRecordGapCenterValue - 431682,
    fullRecordGapCenterValue - 431608,
    fullRecordGapCenterValue - 431590,
    fullRecordGapCenterValue - 431394,
    fullRecordGapCenterValue - 431308,
    fullRecordGapCenterValue - 431092,
    fullRecordGapCenterValue - 431058,
    fullRecordGapCenterValue - 431014,
    fullRecordGapCenterValue - 430888,
    fullRecordGapCenterValue - 430854]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00005_fermat : ∀ n ∈ fullRecordGapRow00005_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00257_not_prime : ¬(recordGapCenter - 435600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435600]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00258_not_prime : ¬(recordGapCenter - 435354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435354]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00259_not_prime : ¬(recordGapCenter - 435322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435322]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00260_not_prime : ¬(recordGapCenter - 435304).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435304]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00261_not_prime : ¬(recordGapCenter - 435154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435154]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00262_not_prime : ¬(recordGapCenter - 435118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 435118]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00263_not_prime : ¬(recordGapCenter - 434998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434998]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00264_not_prime : ¬(recordGapCenter - 434982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434982]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00265_not_prime : ¬(recordGapCenter - 434958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434958]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00266_not_prime : ¬(recordGapCenter - 434914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434914]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00267_not_prime : ¬(recordGapCenter - 434802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434802]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00268_not_prime : ¬(recordGapCenter - 434734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434734]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00269_not_prime : ¬(recordGapCenter - 434572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434572]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00270_not_prime : ¬(recordGapCenter - 434524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434524]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00271_not_prime : ¬(recordGapCenter - 434458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434458]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00272_not_prime : ¬(recordGapCenter - 434410).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434410]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00273_not_prime : ¬(recordGapCenter - 434338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434338]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00274_not_prime : ¬(recordGapCenter - 434314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434314]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00275_not_prime : ¬(recordGapCenter - 434298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434298]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00276_not_prime : ¬(recordGapCenter - 434242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434242]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00277_not_prime : ¬(recordGapCenter - 434202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434202]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00278_not_prime : ¬(recordGapCenter - 434164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434164]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00279_not_prime : ¬(recordGapCenter - 434002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 434002]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00280_not_prime : ¬(recordGapCenter - 433990).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433990]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00281_not_prime : ¬(recordGapCenter - 433894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433894]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00282_not_prime : ¬(recordGapCenter - 433878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433878]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00283_not_prime : ¬(recordGapCenter - 433702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433702]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00284_not_prime : ¬(recordGapCenter - 433684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433684]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00285_not_prime : ¬(recordGapCenter - 433614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433614]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00286_not_prime : ¬(recordGapCenter - 433372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433372]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00287_not_prime : ¬(recordGapCenter - 433282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433282]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00288_not_prime : ¬(recordGapCenter - 433138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433138]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00289_not_prime : ¬(recordGapCenter - 433018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433018]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00290_not_prime : ¬(recordGapCenter - 433002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 433002]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00291_not_prime : ¬(recordGapCenter - 432988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432988]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00292_not_prime : ¬(recordGapCenter - 432910).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432910]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00293_not_prime : ¬(recordGapCenter - 432868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432868]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00294_not_prime : ¬(recordGapCenter - 432862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432862]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00295_not_prime : ¬(recordGapCenter - 432844).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432844]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00296_not_prime : ¬(recordGapCenter - 432802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432802]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00297_not_prime : ¬(recordGapCenter - 432742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432742]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00298_not_prime : ¬(recordGapCenter - 432472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432472]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00299_not_prime : ¬(recordGapCenter - 432462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432462]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00300_not_prime : ¬(recordGapCenter - 432358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432358]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00301_not_prime : ¬(recordGapCenter - 432318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432318]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00302_not_prime : ¬(recordGapCenter - 432070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432070]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00303_not_prime : ¬(recordGapCenter - 432010).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432010]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00304_not_prime : ¬(recordGapCenter - 432000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 432000]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00305_not_prime : ¬(recordGapCenter - 431962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431962]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00306_not_prime : ¬(recordGapCenter - 431944).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431944]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00307_not_prime : ¬(recordGapCenter - 431898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431898]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00308_not_prime : ¬(recordGapCenter - 431890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431890]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00309_not_prime : ¬(recordGapCenter - 431778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431778]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00310_not_prime : ¬(recordGapCenter - 431764).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431764]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00311_not_prime : ¬(recordGapCenter - 431682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431682]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00312_not_prime : ¬(recordGapCenter - 431608).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431608]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00313_not_prime : ¬(recordGapCenter - 431590).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431590]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00314_not_prime : ¬(recordGapCenter - 431394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431394]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00315_not_prime : ¬(recordGapCenter - 431308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431308]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00316_not_prime : ¬(recordGapCenter - 431092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431092]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00317_not_prime : ¬(recordGapCenter - 431058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431058]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00318_not_prime : ¬(recordGapCenter - 431014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 431014]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00319_not_prime : ¬(recordGapCenter - 430888).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430888]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm00320_not_prime : ¬(recordGapCenter - 430854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 430854]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

end PrimeFactorUnimodality
