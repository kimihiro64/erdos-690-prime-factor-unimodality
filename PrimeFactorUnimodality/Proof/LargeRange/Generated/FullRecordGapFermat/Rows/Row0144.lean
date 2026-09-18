import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00144_values : List Nat :=
  [fullRecordGapCenterValue + 548342,
    fullRecordGapCenterValue + 548348,
    fullRecordGapCenterValue + 548426,
    fullRecordGapCenterValue + 548486,
    fullRecordGapCenterValue + 548510,
    fullRecordGapCenterValue + 548538,
    fullRecordGapCenterValue + 548732,
    fullRecordGapCenterValue + 548958,
    fullRecordGapCenterValue + 549012,
    fullRecordGapCenterValue + 549078,
    fullRecordGapCenterValue + 549092,
    fullRecordGapCenterValue + 549158,
    fullRecordGapCenterValue + 549218,
    fullRecordGapCenterValue + 549272,
    fullRecordGapCenterValue + 549348,
    fullRecordGapCenterValue + 549386,
    fullRecordGapCenterValue + 549426,
    fullRecordGapCenterValue + 549452,
    fullRecordGapCenterValue + 549476,
    fullRecordGapCenterValue + 549566,
    fullRecordGapCenterValue + 549596,
    fullRecordGapCenterValue + 549812,
    fullRecordGapCenterValue + 549852,
    fullRecordGapCenterValue + 549876,
    fullRecordGapCenterValue + 549932,
    fullRecordGapCenterValue + 549992,
    fullRecordGapCenterValue + 550092,
    fullRecordGapCenterValue + 550146,
    fullRecordGapCenterValue + 550148,
    fullRecordGapCenterValue + 550218,
    fullRecordGapCenterValue + 550236,
    fullRecordGapCenterValue + 550266,
    fullRecordGapCenterValue + 550268,
    fullRecordGapCenterValue + 550292,
    fullRecordGapCenterValue + 550328,
    fullRecordGapCenterValue + 550428,
    fullRecordGapCenterValue + 550490,
    fullRecordGapCenterValue + 550526,
    fullRecordGapCenterValue + 550716,
    fullRecordGapCenterValue + 550778,
    fullRecordGapCenterValue + 550790,
    fullRecordGapCenterValue + 550806,
    fullRecordGapCenterValue + 550838,
    fullRecordGapCenterValue + 550938,
    fullRecordGapCenterValue + 551006,
    fullRecordGapCenterValue + 551042,
    fullRecordGapCenterValue + 551048,
    fullRecordGapCenterValue + 551108,
    fullRecordGapCenterValue + 551238,
    fullRecordGapCenterValue + 551246,
    fullRecordGapCenterValue + 551336,
    fullRecordGapCenterValue + 551436,
    fullRecordGapCenterValue + 551468,
    fullRecordGapCenterValue + 551546,
    fullRecordGapCenterValue + 551630,
    fullRecordGapCenterValue + 551636,
    fullRecordGapCenterValue + 551658,
    fullRecordGapCenterValue + 551762,
    fullRecordGapCenterValue + 551828,
    fullRecordGapCenterValue + 551846,
    fullRecordGapCenterValue + 551868,
    fullRecordGapCenterValue + 551882,
    fullRecordGapCenterValue + 551982,
    fullRecordGapCenterValue + 551996]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00144_fermat : ∀ n ∈ fullRecordGapRow00144_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09153_not_prime : ¬(recordGapCenter + 548342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 548342]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09154_not_prime : ¬(recordGapCenter + 548348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 548348]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09155_not_prime : ¬(recordGapCenter + 548426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 548426]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09156_not_prime : ¬(recordGapCenter + 548486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 548486]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09157_not_prime : ¬(recordGapCenter + 548510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 548510]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09158_not_prime : ¬(recordGapCenter + 548538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 548538]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09159_not_prime : ¬(recordGapCenter + 548732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 548732]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09160_not_prime : ¬(recordGapCenter + 548958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 548958]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09161_not_prime : ¬(recordGapCenter + 549012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549012]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09162_not_prime : ¬(recordGapCenter + 549078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549078]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09163_not_prime : ¬(recordGapCenter + 549092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549092]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09164_not_prime : ¬(recordGapCenter + 549158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549158]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09165_not_prime : ¬(recordGapCenter + 549218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549218]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09166_not_prime : ¬(recordGapCenter + 549272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549272]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09167_not_prime : ¬(recordGapCenter + 549348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549348]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09168_not_prime : ¬(recordGapCenter + 549386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549386]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09169_not_prime : ¬(recordGapCenter + 549426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549426]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09170_not_prime : ¬(recordGapCenter + 549452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549452]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09171_not_prime : ¬(recordGapCenter + 549476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549476]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09172_not_prime : ¬(recordGapCenter + 549566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549566]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09173_not_prime : ¬(recordGapCenter + 549596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549596]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09174_not_prime : ¬(recordGapCenter + 549812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549812]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09175_not_prime : ¬(recordGapCenter + 549852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549852]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09176_not_prime : ¬(recordGapCenter + 549876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549876]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09177_not_prime : ¬(recordGapCenter + 549932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549932]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09178_not_prime : ¬(recordGapCenter + 549992).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 549992]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09179_not_prime : ¬(recordGapCenter + 550092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550092]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09180_not_prime : ¬(recordGapCenter + 550146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550146]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09181_not_prime : ¬(recordGapCenter + 550148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550148]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09182_not_prime : ¬(recordGapCenter + 550218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550218]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09183_not_prime : ¬(recordGapCenter + 550236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550236]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09184_not_prime : ¬(recordGapCenter + 550266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550266]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09185_not_prime : ¬(recordGapCenter + 550268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550268]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09186_not_prime : ¬(recordGapCenter + 550292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550292]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09187_not_prime : ¬(recordGapCenter + 550328).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550328]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09188_not_prime : ¬(recordGapCenter + 550428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550428]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09189_not_prime : ¬(recordGapCenter + 550490).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550490]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09190_not_prime : ¬(recordGapCenter + 550526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550526]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09191_not_prime : ¬(recordGapCenter + 550716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550716]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09192_not_prime : ¬(recordGapCenter + 550778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550778]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09193_not_prime : ¬(recordGapCenter + 550790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550790]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09194_not_prime : ¬(recordGapCenter + 550806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550806]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09195_not_prime : ¬(recordGapCenter + 550838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550838]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09196_not_prime : ¬(recordGapCenter + 550938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 550938]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09197_not_prime : ¬(recordGapCenter + 551006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551006]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09198_not_prime : ¬(recordGapCenter + 551042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551042]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09199_not_prime : ¬(recordGapCenter + 551048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551048]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09200_not_prime : ¬(recordGapCenter + 551108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551108]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09201_not_prime : ¬(recordGapCenter + 551238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551238]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09202_not_prime : ¬(recordGapCenter + 551246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551246]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09203_not_prime : ¬(recordGapCenter + 551336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551336]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09204_not_prime : ¬(recordGapCenter + 551436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551436]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09205_not_prime : ¬(recordGapCenter + 551468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551468]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09206_not_prime : ¬(recordGapCenter + 551546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551546]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09207_not_prime : ¬(recordGapCenter + 551630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551630]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09208_not_prime : ¬(recordGapCenter + 551636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551636]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09209_not_prime : ¬(recordGapCenter + 551658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551658]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09210_not_prime : ¬(recordGapCenter + 551762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551762]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09211_not_prime : ¬(recordGapCenter + 551828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551828]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09212_not_prime : ¬(recordGapCenter + 551846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551846]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09213_not_prime : ¬(recordGapCenter + 551868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551868]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09214_not_prime : ¬(recordGapCenter + 551882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551882]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09215_not_prime : ¬(recordGapCenter + 551982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551982]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

theorem fullRecordGapTerm09216_not_prime : ¬(recordGapCenter + 551996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 551996]
  · apply fullRecordGapRow00144_fermat
    simp [fullRecordGapRow00144_values]

end PrimeFactorUnimodality
