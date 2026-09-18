import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00009_values : List Nat :=
  [fullRecordGapCenterValue - 414892,
    fullRecordGapCenterValue - 414802,
    fullRecordGapCenterValue - 414762,
    fullRecordGapCenterValue - 414724,
    fullRecordGapCenterValue - 414720,
    fullRecordGapCenterValue - 414714,
    fullRecordGapCenterValue - 414658,
    fullRecordGapCenterValue - 414628,
    fullRecordGapCenterValue - 414574,
    fullRecordGapCenterValue - 414514,
    fullRecordGapCenterValue - 414424,
    fullRecordGapCenterValue - 414402,
    fullRecordGapCenterValue - 414382,
    fullRecordGapCenterValue - 414292,
    fullRecordGapCenterValue - 414174,
    fullRecordGapCenterValue - 413952,
    fullRecordGapCenterValue - 413878,
    fullRecordGapCenterValue - 413794,
    fullRecordGapCenterValue - 413682,
    fullRecordGapCenterValue - 413572,
    fullRecordGapCenterValue - 413562,
    fullRecordGapCenterValue - 413454,
    fullRecordGapCenterValue - 413332,
    fullRecordGapCenterValue - 413272,
    fullRecordGapCenterValue - 413194,
    fullRecordGapCenterValue - 413178,
    fullRecordGapCenterValue - 412978,
    fullRecordGapCenterValue - 412954,
    fullRecordGapCenterValue - 412914,
    fullRecordGapCenterValue - 412792,
    fullRecordGapCenterValue - 412732,
    fullRecordGapCenterValue - 412662,
    fullRecordGapCenterValue - 412564,
    fullRecordGapCenterValue - 412498,
    fullRecordGapCenterValue - 412492,
    fullRecordGapCenterValue - 412474,
    fullRecordGapCenterValue - 412458,
    fullRecordGapCenterValue - 412374,
    fullRecordGapCenterValue - 412354,
    fullRecordGapCenterValue - 412194,
    fullRecordGapCenterValue - 412078,
    fullRecordGapCenterValue - 412018,
    fullRecordGapCenterValue - 411934,
    fullRecordGapCenterValue - 411898,
    fullRecordGapCenterValue - 411834,
    fullRecordGapCenterValue - 411798,
    fullRecordGapCenterValue - 411724,
    fullRecordGapCenterValue - 411694,
    fullRecordGapCenterValue - 411688,
    fullRecordGapCenterValue - 411600,
    fullRecordGapCenterValue - 411592,
    fullRecordGapCenterValue - 411402,
    fullRecordGapCenterValue - 411058,
    fullRecordGapCenterValue - 410974,
    fullRecordGapCenterValue - 410728,
    fullRecordGapCenterValue - 410694,
    fullRecordGapCenterValue - 410692,
    fullRecordGapCenterValue - 410682,
    fullRecordGapCenterValue - 410668,
    fullRecordGapCenterValue - 410638,
    fullRecordGapCenterValue - 410314,
    fullRecordGapCenterValue - 410302,
    fullRecordGapCenterValue - 410104,
    fullRecordGapCenterValue - 410092]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00009_fermat : ∀ n ∈ fullRecordGapRow00009_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00513_not_prime : ¬(recordGapCenter - 414892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414892]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00514_not_prime : ¬(recordGapCenter - 414802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414802]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00515_not_prime : ¬(recordGapCenter - 414762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414762]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00516_not_prime : ¬(recordGapCenter - 414724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414724]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00517_not_prime : ¬(recordGapCenter - 414720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414720]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00518_not_prime : ¬(recordGapCenter - 414714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414714]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00519_not_prime : ¬(recordGapCenter - 414658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414658]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00520_not_prime : ¬(recordGapCenter - 414628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414628]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00521_not_prime : ¬(recordGapCenter - 414574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414574]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00522_not_prime : ¬(recordGapCenter - 414514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414514]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00523_not_prime : ¬(recordGapCenter - 414424).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414424]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00524_not_prime : ¬(recordGapCenter - 414402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414402]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00525_not_prime : ¬(recordGapCenter - 414382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414382]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00526_not_prime : ¬(recordGapCenter - 414292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414292]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00527_not_prime : ¬(recordGapCenter - 414174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414174]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00528_not_prime : ¬(recordGapCenter - 413952).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413952]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00529_not_prime : ¬(recordGapCenter - 413878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413878]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00530_not_prime : ¬(recordGapCenter - 413794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413794]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00531_not_prime : ¬(recordGapCenter - 413682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413682]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00532_not_prime : ¬(recordGapCenter - 413572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413572]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00533_not_prime : ¬(recordGapCenter - 413562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413562]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00534_not_prime : ¬(recordGapCenter - 413454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413454]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00535_not_prime : ¬(recordGapCenter - 413332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413332]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00536_not_prime : ¬(recordGapCenter - 413272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413272]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00537_not_prime : ¬(recordGapCenter - 413194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413194]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00538_not_prime : ¬(recordGapCenter - 413178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 413178]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00539_not_prime : ¬(recordGapCenter - 412978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412978]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00540_not_prime : ¬(recordGapCenter - 412954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412954]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00541_not_prime : ¬(recordGapCenter - 412914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412914]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00542_not_prime : ¬(recordGapCenter - 412792).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412792]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00543_not_prime : ¬(recordGapCenter - 412732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412732]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00544_not_prime : ¬(recordGapCenter - 412662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412662]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00545_not_prime : ¬(recordGapCenter - 412564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412564]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00546_not_prime : ¬(recordGapCenter - 412498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412498]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00547_not_prime : ¬(recordGapCenter - 412492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412492]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00548_not_prime : ¬(recordGapCenter - 412474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412474]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00549_not_prime : ¬(recordGapCenter - 412458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412458]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00550_not_prime : ¬(recordGapCenter - 412374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412374]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00551_not_prime : ¬(recordGapCenter - 412354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412354]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00552_not_prime : ¬(recordGapCenter - 412194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412194]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00553_not_prime : ¬(recordGapCenter - 412078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412078]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00554_not_prime : ¬(recordGapCenter - 412018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 412018]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00555_not_prime : ¬(recordGapCenter - 411934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411934]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00556_not_prime : ¬(recordGapCenter - 411898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411898]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00557_not_prime : ¬(recordGapCenter - 411834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411834]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00558_not_prime : ¬(recordGapCenter - 411798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411798]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00559_not_prime : ¬(recordGapCenter - 411724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411724]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00560_not_prime : ¬(recordGapCenter - 411694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411694]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00561_not_prime : ¬(recordGapCenter - 411688).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411688]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00562_not_prime : ¬(recordGapCenter - 411600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411600]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00563_not_prime : ¬(recordGapCenter - 411592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411592]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00564_not_prime : ¬(recordGapCenter - 411402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411402]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00565_not_prime : ¬(recordGapCenter - 411058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 411058]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00566_not_prime : ¬(recordGapCenter - 410974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410974]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00567_not_prime : ¬(recordGapCenter - 410728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410728]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00568_not_prime : ¬(recordGapCenter - 410694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410694]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00569_not_prime : ¬(recordGapCenter - 410692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410692]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00570_not_prime : ¬(recordGapCenter - 410682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410682]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00571_not_prime : ¬(recordGapCenter - 410668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410668]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00572_not_prime : ¬(recordGapCenter - 410638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410638]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00573_not_prime : ¬(recordGapCenter - 410314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410314]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00574_not_prime : ¬(recordGapCenter - 410302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410302]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00575_not_prime : ¬(recordGapCenter - 410104).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410104]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

theorem fullRecordGapTerm00576_not_prime : ¬(recordGapCenter - 410092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 410092]
  · apply fullRecordGapRow00009_fermat
    simp [fullRecordGapRow00009_values]

end PrimeFactorUnimodality
