import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00034_values : List Nat :=
  [fullRecordGapCenterValue - 283174,
    fullRecordGapCenterValue - 283134,
    fullRecordGapCenterValue - 282994,
    fullRecordGapCenterValue - 282922,
    fullRecordGapCenterValue - 282868,
    fullRecordGapCenterValue - 282774,
    fullRecordGapCenterValue - 282508,
    fullRecordGapCenterValue - 282442,
    fullRecordGapCenterValue - 282354,
    fullRecordGapCenterValue - 282292,
    fullRecordGapCenterValue - 282214,
    fullRecordGapCenterValue - 282102,
    fullRecordGapCenterValue - 281734,
    fullRecordGapCenterValue - 281518,
    fullRecordGapCenterValue - 281458,
    fullRecordGapCenterValue - 281434,
    fullRecordGapCenterValue - 281262,
    fullRecordGapCenterValue - 280954,
    fullRecordGapCenterValue - 280762,
    fullRecordGapCenterValue - 280594,
    fullRecordGapCenterValue - 280564,
    fullRecordGapCenterValue - 280542,
    fullRecordGapCenterValue - 280468,
    fullRecordGapCenterValue - 280362,
    fullRecordGapCenterValue - 280342,
    fullRecordGapCenterValue - 280338,
    fullRecordGapCenterValue - 280122,
    fullRecordGapCenterValue - 280012,
    fullRecordGapCenterValue - 279988,
    fullRecordGapCenterValue - 279982,
    fullRecordGapCenterValue - 279934,
    fullRecordGapCenterValue - 279834,
    fullRecordGapCenterValue - 279814,
    fullRecordGapCenterValue - 279724,
    fullRecordGapCenterValue - 279534,
    fullRecordGapCenterValue - 279478,
    fullRecordGapCenterValue - 279418,
    fullRecordGapCenterValue - 279402,
    fullRecordGapCenterValue - 279388,
    fullRecordGapCenterValue - 279178,
    fullRecordGapCenterValue - 279142,
    fullRecordGapCenterValue - 278934,
    fullRecordGapCenterValue - 278862,
    fullRecordGapCenterValue - 278742,
    fullRecordGapCenterValue - 278682,
    fullRecordGapCenterValue - 278644,
    fullRecordGapCenterValue - 278602,
    fullRecordGapCenterValue - 278394,
    fullRecordGapCenterValue - 278374,
    fullRecordGapCenterValue - 278338,
    fullRecordGapCenterValue - 278218,
    fullRecordGapCenterValue - 278158,
    fullRecordGapCenterValue - 277954,
    fullRecordGapCenterValue - 277918,
    fullRecordGapCenterValue - 277834,
    fullRecordGapCenterValue - 277828,
    fullRecordGapCenterValue - 277738,
    fullRecordGapCenterValue - 277708,
    fullRecordGapCenterValue - 277674,
    fullRecordGapCenterValue - 277638,
    fullRecordGapCenterValue - 277462,
    fullRecordGapCenterValue - 277374,
    fullRecordGapCenterValue - 277294,
    fullRecordGapCenterValue - 277252]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00034_fermat : ∀ n ∈ fullRecordGapRow00034_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02113_not_prime : ¬(recordGapCenter - 283174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283174]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02114_not_prime : ¬(recordGapCenter - 283134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 283134]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02115_not_prime : ¬(recordGapCenter - 282994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282994]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02116_not_prime : ¬(recordGapCenter - 282922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282922]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02117_not_prime : ¬(recordGapCenter - 282868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282868]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02118_not_prime : ¬(recordGapCenter - 282774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282774]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02119_not_prime : ¬(recordGapCenter - 282508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282508]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02120_not_prime : ¬(recordGapCenter - 282442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282442]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02121_not_prime : ¬(recordGapCenter - 282354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282354]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02122_not_prime : ¬(recordGapCenter - 282292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282292]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02123_not_prime : ¬(recordGapCenter - 282214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282214]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02124_not_prime : ¬(recordGapCenter - 282102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 282102]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02125_not_prime : ¬(recordGapCenter - 281734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 281734]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02126_not_prime : ¬(recordGapCenter - 281518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 281518]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02127_not_prime : ¬(recordGapCenter - 281458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 281458]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02128_not_prime : ¬(recordGapCenter - 281434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 281434]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02129_not_prime : ¬(recordGapCenter - 281262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 281262]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02130_not_prime : ¬(recordGapCenter - 280954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280954]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02131_not_prime : ¬(recordGapCenter - 280762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280762]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02132_not_prime : ¬(recordGapCenter - 280594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280594]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02133_not_prime : ¬(recordGapCenter - 280564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280564]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02134_not_prime : ¬(recordGapCenter - 280542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280542]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02135_not_prime : ¬(recordGapCenter - 280468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280468]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02136_not_prime : ¬(recordGapCenter - 280362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280362]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02137_not_prime : ¬(recordGapCenter - 280342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280342]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02138_not_prime : ¬(recordGapCenter - 280338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280338]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02139_not_prime : ¬(recordGapCenter - 280122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280122]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02140_not_prime : ¬(recordGapCenter - 280012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 280012]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02141_not_prime : ¬(recordGapCenter - 279988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279988]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02142_not_prime : ¬(recordGapCenter - 279982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279982]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02143_not_prime : ¬(recordGapCenter - 279934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279934]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02144_not_prime : ¬(recordGapCenter - 279834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279834]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02145_not_prime : ¬(recordGapCenter - 279814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279814]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02146_not_prime : ¬(recordGapCenter - 279724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279724]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02147_not_prime : ¬(recordGapCenter - 279534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279534]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02148_not_prime : ¬(recordGapCenter - 279478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279478]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02149_not_prime : ¬(recordGapCenter - 279418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279418]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02150_not_prime : ¬(recordGapCenter - 279402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279402]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02151_not_prime : ¬(recordGapCenter - 279388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279388]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02152_not_prime : ¬(recordGapCenter - 279178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279178]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02153_not_prime : ¬(recordGapCenter - 279142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 279142]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02154_not_prime : ¬(recordGapCenter - 278934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278934]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02155_not_prime : ¬(recordGapCenter - 278862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278862]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02156_not_prime : ¬(recordGapCenter - 278742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278742]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02157_not_prime : ¬(recordGapCenter - 278682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278682]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02158_not_prime : ¬(recordGapCenter - 278644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278644]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02159_not_prime : ¬(recordGapCenter - 278602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278602]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02160_not_prime : ¬(recordGapCenter - 278394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278394]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02161_not_prime : ¬(recordGapCenter - 278374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278374]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02162_not_prime : ¬(recordGapCenter - 278338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278338]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02163_not_prime : ¬(recordGapCenter - 278218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278218]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02164_not_prime : ¬(recordGapCenter - 278158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 278158]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02165_not_prime : ¬(recordGapCenter - 277954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277954]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02166_not_prime : ¬(recordGapCenter - 277918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277918]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02167_not_prime : ¬(recordGapCenter - 277834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277834]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02168_not_prime : ¬(recordGapCenter - 277828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277828]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02169_not_prime : ¬(recordGapCenter - 277738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277738]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02170_not_prime : ¬(recordGapCenter - 277708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277708]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02171_not_prime : ¬(recordGapCenter - 277674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277674]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02172_not_prime : ¬(recordGapCenter - 277638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277638]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02173_not_prime : ¬(recordGapCenter - 277462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277462]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02174_not_prime : ¬(recordGapCenter - 277374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277374]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02175_not_prime : ¬(recordGapCenter - 277294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277294]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

theorem fullRecordGapTerm02176_not_prime : ¬(recordGapCenter - 277252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277252]
  · apply fullRecordGapRow00034_fermat
    simp [fullRecordGapRow00034_values]

end PrimeFactorUnimodality
