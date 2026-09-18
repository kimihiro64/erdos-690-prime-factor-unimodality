import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00038_values : List Nat :=
  [fullRecordGapCenterValue - 259878,
    fullRecordGapCenterValue - 259804,
    fullRecordGapCenterValue - 259564,
    fullRecordGapCenterValue - 259342,
    fullRecordGapCenterValue - 259338,
    fullRecordGapCenterValue - 259308,
    fullRecordGapCenterValue - 259282,
    fullRecordGapCenterValue - 259132,
    fullRecordGapCenterValue - 259062,
    fullRecordGapCenterValue - 259018,
    fullRecordGapCenterValue - 258954,
    fullRecordGapCenterValue - 258898,
    fullRecordGapCenterValue - 258720,
    fullRecordGapCenterValue - 258694,
    fullRecordGapCenterValue - 258484,
    fullRecordGapCenterValue - 258418,
    fullRecordGapCenterValue - 258178,
    fullRecordGapCenterValue - 258022,
    fullRecordGapCenterValue - 257962,
    fullRecordGapCenterValue - 257878,
    fullRecordGapCenterValue - 257674,
    fullRecordGapCenterValue - 257662,
    fullRecordGapCenterValue - 257638,
    fullRecordGapCenterValue - 257434,
    fullRecordGapCenterValue - 257332,
    fullRecordGapCenterValue - 257308,
    fullRecordGapCenterValue - 257098,
    fullRecordGapCenterValue - 257038,
    fullRecordGapCenterValue - 256948,
    fullRecordGapCenterValue - 256822,
    fullRecordGapCenterValue - 256798,
    fullRecordGapCenterValue - 256702,
    fullRecordGapCenterValue - 256608,
    fullRecordGapCenterValue - 256324,
    fullRecordGapCenterValue - 256252,
    fullRecordGapCenterValue - 256198,
    fullRecordGapCenterValue - 256132,
    fullRecordGapCenterValue - 255988,
    fullRecordGapCenterValue - 255862,
    fullRecordGapCenterValue - 255628,
    fullRecordGapCenterValue - 255552,
    fullRecordGapCenterValue - 255412,
    fullRecordGapCenterValue - 254578,
    fullRecordGapCenterValue - 254482,
    fullRecordGapCenterValue - 254404,
    fullRecordGapCenterValue - 254314,
    fullRecordGapCenterValue - 254278,
    fullRecordGapCenterValue - 254074,
    fullRecordGapCenterValue - 254062,
    fullRecordGapCenterValue - 253852,
    fullRecordGapCenterValue - 253714,
    fullRecordGapCenterValue - 253684,
    fullRecordGapCenterValue - 253678,
    fullRecordGapCenterValue - 253654,
    fullRecordGapCenterValue - 253564,
    fullRecordGapCenterValue - 253468,
    fullRecordGapCenterValue - 253440,
    fullRecordGapCenterValue - 253348,
    fullRecordGapCenterValue - 253252,
    fullRecordGapCenterValue - 253222,
    fullRecordGapCenterValue - 252622,
    fullRecordGapCenterValue - 252514,
    fullRecordGapCenterValue - 252508,
    fullRecordGapCenterValue - 252412]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00038_fermat : ∀ n ∈ fullRecordGapRow00038_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02369_not_prime : ¬(recordGapCenter - 259878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259878]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02370_not_prime : ¬(recordGapCenter - 259804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259804]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02371_not_prime : ¬(recordGapCenter - 259564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259564]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02372_not_prime : ¬(recordGapCenter - 259342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259342]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02373_not_prime : ¬(recordGapCenter - 259338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259338]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02374_not_prime : ¬(recordGapCenter - 259308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259308]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02375_not_prime : ¬(recordGapCenter - 259282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259282]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02376_not_prime : ¬(recordGapCenter - 259132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259132]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02377_not_prime : ¬(recordGapCenter - 259062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259062]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02378_not_prime : ¬(recordGapCenter - 259018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259018]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02379_not_prime : ¬(recordGapCenter - 258954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258954]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02380_not_prime : ¬(recordGapCenter - 258898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258898]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02381_not_prime : ¬(recordGapCenter - 258720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258720]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02382_not_prime : ¬(recordGapCenter - 258694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258694]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02383_not_prime : ¬(recordGapCenter - 258484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258484]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02384_not_prime : ¬(recordGapCenter - 258418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258418]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02385_not_prime : ¬(recordGapCenter - 258178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258178]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02386_not_prime : ¬(recordGapCenter - 258022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258022]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02387_not_prime : ¬(recordGapCenter - 257962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257962]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02388_not_prime : ¬(recordGapCenter - 257878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257878]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02389_not_prime : ¬(recordGapCenter - 257674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257674]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02390_not_prime : ¬(recordGapCenter - 257662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257662]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02391_not_prime : ¬(recordGapCenter - 257638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257638]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02392_not_prime : ¬(recordGapCenter - 257434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257434]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02393_not_prime : ¬(recordGapCenter - 257332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257332]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02394_not_prime : ¬(recordGapCenter - 257308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257308]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02395_not_prime : ¬(recordGapCenter - 257098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257098]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02396_not_prime : ¬(recordGapCenter - 257038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257038]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02397_not_prime : ¬(recordGapCenter - 256948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256948]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02398_not_prime : ¬(recordGapCenter - 256822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256822]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02399_not_prime : ¬(recordGapCenter - 256798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256798]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02400_not_prime : ¬(recordGapCenter - 256702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256702]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02401_not_prime : ¬(recordGapCenter - 256608).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256608]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02402_not_prime : ¬(recordGapCenter - 256324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256324]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02403_not_prime : ¬(recordGapCenter - 256252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256252]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02404_not_prime : ¬(recordGapCenter - 256198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256198]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02405_not_prime : ¬(recordGapCenter - 256132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256132]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02406_not_prime : ¬(recordGapCenter - 255988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 255988]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02407_not_prime : ¬(recordGapCenter - 255862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 255862]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02408_not_prime : ¬(recordGapCenter - 255628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 255628]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02409_not_prime : ¬(recordGapCenter - 255552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 255552]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02410_not_prime : ¬(recordGapCenter - 255412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 255412]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02411_not_prime : ¬(recordGapCenter - 254578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 254578]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02412_not_prime : ¬(recordGapCenter - 254482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 254482]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02413_not_prime : ¬(recordGapCenter - 254404).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 254404]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02414_not_prime : ¬(recordGapCenter - 254314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 254314]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02415_not_prime : ¬(recordGapCenter - 254278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 254278]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02416_not_prime : ¬(recordGapCenter - 254074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 254074]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02417_not_prime : ¬(recordGapCenter - 254062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 254062]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02418_not_prime : ¬(recordGapCenter - 253852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253852]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02419_not_prime : ¬(recordGapCenter - 253714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253714]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02420_not_prime : ¬(recordGapCenter - 253684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253684]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02421_not_prime : ¬(recordGapCenter - 253678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253678]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02422_not_prime : ¬(recordGapCenter - 253654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253654]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02423_not_prime : ¬(recordGapCenter - 253564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253564]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02424_not_prime : ¬(recordGapCenter - 253468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253468]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02425_not_prime : ¬(recordGapCenter - 253440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253440]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02426_not_prime : ¬(recordGapCenter - 253348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253348]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02427_not_prime : ¬(recordGapCenter - 253252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253252]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02428_not_prime : ¬(recordGapCenter - 253222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253222]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02429_not_prime : ¬(recordGapCenter - 252622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252622]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02430_not_prime : ¬(recordGapCenter - 252514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252514]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02431_not_prime : ¬(recordGapCenter - 252508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252508]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

theorem fullRecordGapTerm02432_not_prime : ¬(recordGapCenter - 252412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252412]
  · apply fullRecordGapRow00038_fermat
    simp [fullRecordGapRow00038_values]

end PrimeFactorUnimodality
