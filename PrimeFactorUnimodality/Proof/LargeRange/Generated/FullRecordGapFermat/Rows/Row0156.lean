import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00156_values : List Nat :=
  [fullRecordGapCenterValue + 596396,
    fullRecordGapCenterValue + 596408,
    fullRecordGapCenterValue + 596426,
    fullRecordGapCenterValue + 596522,
    fullRecordGapCenterValue + 596586,
    fullRecordGapCenterValue + 596606,
    fullRecordGapCenterValue + 596612,
    fullRecordGapCenterValue + 596678,
    fullRecordGapCenterValue + 596690,
    fullRecordGapCenterValue + 596732,
    fullRecordGapCenterValue + 596738,
    fullRecordGapCenterValue + 596822,
    fullRecordGapCenterValue + 596888,
    fullRecordGapCenterValue + 596982,
    fullRecordGapCenterValue + 596996,
    fullRecordGapCenterValue + 597026,
    fullRecordGapCenterValue + 597158,
    fullRecordGapCenterValue + 597242,
    fullRecordGapCenterValue + 597306,
    fullRecordGapCenterValue + 597396,
    fullRecordGapCenterValue + 597446,
    fullRecordGapCenterValue + 597518,
    fullRecordGapCenterValue + 597572,
    fullRecordGapCenterValue + 597612,
    fullRecordGapCenterValue + 597642,
    fullRecordGapCenterValue + 597656,
    fullRecordGapCenterValue + 597738,
    fullRecordGapCenterValue + 597836,
    fullRecordGapCenterValue + 597858,
    fullRecordGapCenterValue + 597966,
    fullRecordGapCenterValue + 597972,
    fullRecordGapCenterValue + 597986,
    fullRecordGapCenterValue + 598232,
    fullRecordGapCenterValue + 598236,
    fullRecordGapCenterValue + 598358,
    fullRecordGapCenterValue + 598398,
    fullRecordGapCenterValue + 598412,
    fullRecordGapCenterValue + 598508,
    fullRecordGapCenterValue + 598568,
    fullRecordGapCenterValue + 598622,
    fullRecordGapCenterValue + 598692,
    fullRecordGapCenterValue + 598790,
    fullRecordGapCenterValue + 598868,
    fullRecordGapCenterValue + 598916,
    fullRecordGapCenterValue + 598938,
    fullRecordGapCenterValue + 598950,
    fullRecordGapCenterValue + 599036,
    fullRecordGapCenterValue + 599042,
    fullRecordGapCenterValue + 599096,
    fullRecordGapCenterValue + 599226,
    fullRecordGapCenterValue + 599246,
    fullRecordGapCenterValue + 599316,
    fullRecordGapCenterValue + 599348,
    fullRecordGapCenterValue + 599432,
    fullRecordGapCenterValue + 599462,
    fullRecordGapCenterValue + 599468,
    fullRecordGapCenterValue + 599510,
    fullRecordGapCenterValue + 599810,
    fullRecordGapCenterValue + 599988,
    fullRecordGapCenterValue + 600000,
    fullRecordGapCenterValue + 600170,
    fullRecordGapCenterValue + 600252,
    fullRecordGapCenterValue + 600258,
    fullRecordGapCenterValue + 600276]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00156_fermat : ∀ n ∈ fullRecordGapRow00156_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09921_not_prime : ¬(recordGapCenter + 596396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596396]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09922_not_prime : ¬(recordGapCenter + 596408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596408]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09923_not_prime : ¬(recordGapCenter + 596426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596426]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09924_not_prime : ¬(recordGapCenter + 596522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596522]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09925_not_prime : ¬(recordGapCenter + 596586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596586]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09926_not_prime : ¬(recordGapCenter + 596606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596606]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09927_not_prime : ¬(recordGapCenter + 596612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596612]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09928_not_prime : ¬(recordGapCenter + 596678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596678]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09929_not_prime : ¬(recordGapCenter + 596690).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596690]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09930_not_prime : ¬(recordGapCenter + 596732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596732]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09931_not_prime : ¬(recordGapCenter + 596738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596738]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09932_not_prime : ¬(recordGapCenter + 596822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596822]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09933_not_prime : ¬(recordGapCenter + 596888).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596888]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09934_not_prime : ¬(recordGapCenter + 596982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596982]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09935_not_prime : ¬(recordGapCenter + 596996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 596996]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09936_not_prime : ¬(recordGapCenter + 597026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597026]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09937_not_prime : ¬(recordGapCenter + 597158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597158]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09938_not_prime : ¬(recordGapCenter + 597242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597242]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09939_not_prime : ¬(recordGapCenter + 597306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597306]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09940_not_prime : ¬(recordGapCenter + 597396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597396]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09941_not_prime : ¬(recordGapCenter + 597446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597446]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09942_not_prime : ¬(recordGapCenter + 597518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597518]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09943_not_prime : ¬(recordGapCenter + 597572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597572]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09944_not_prime : ¬(recordGapCenter + 597612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597612]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09945_not_prime : ¬(recordGapCenter + 597642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597642]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09946_not_prime : ¬(recordGapCenter + 597656).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597656]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09947_not_prime : ¬(recordGapCenter + 597738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597738]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09948_not_prime : ¬(recordGapCenter + 597836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597836]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09949_not_prime : ¬(recordGapCenter + 597858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597858]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09950_not_prime : ¬(recordGapCenter + 597966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597966]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09951_not_prime : ¬(recordGapCenter + 597972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597972]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09952_not_prime : ¬(recordGapCenter + 597986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 597986]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09953_not_prime : ¬(recordGapCenter + 598232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 598232]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09954_not_prime : ¬(recordGapCenter + 598236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 598236]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09955_not_prime : ¬(recordGapCenter + 598358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 598358]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09956_not_prime : ¬(recordGapCenter + 598398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 598398]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09957_not_prime : ¬(recordGapCenter + 598412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 598412]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09958_not_prime : ¬(recordGapCenter + 598508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 598508]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09959_not_prime : ¬(recordGapCenter + 598568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 598568]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09960_not_prime : ¬(recordGapCenter + 598622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 598622]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09961_not_prime : ¬(recordGapCenter + 598692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 598692]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09962_not_prime : ¬(recordGapCenter + 598790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 598790]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09963_not_prime : ¬(recordGapCenter + 598868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 598868]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09964_not_prime : ¬(recordGapCenter + 598916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 598916]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09965_not_prime : ¬(recordGapCenter + 598938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 598938]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09966_not_prime : ¬(recordGapCenter + 598950).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 598950]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09967_not_prime : ¬(recordGapCenter + 599036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 599036]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09968_not_prime : ¬(recordGapCenter + 599042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 599042]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09969_not_prime : ¬(recordGapCenter + 599096).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 599096]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09970_not_prime : ¬(recordGapCenter + 599226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 599226]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09971_not_prime : ¬(recordGapCenter + 599246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 599246]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09972_not_prime : ¬(recordGapCenter + 599316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 599316]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09973_not_prime : ¬(recordGapCenter + 599348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 599348]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09974_not_prime : ¬(recordGapCenter + 599432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 599432]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09975_not_prime : ¬(recordGapCenter + 599462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 599462]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09976_not_prime : ¬(recordGapCenter + 599468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 599468]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09977_not_prime : ¬(recordGapCenter + 599510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 599510]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09978_not_prime : ¬(recordGapCenter + 599810).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 599810]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09979_not_prime : ¬(recordGapCenter + 599988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 599988]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09980_not_prime : ¬(recordGapCenter + 600000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 600000]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09981_not_prime : ¬(recordGapCenter + 600170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 600170]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09982_not_prime : ¬(recordGapCenter + 600252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 600252]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09983_not_prime : ¬(recordGapCenter + 600258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 600258]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

theorem fullRecordGapTerm09984_not_prime : ¬(recordGapCenter + 600276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 600276]
  · apply fullRecordGapRow00156_fermat
    simp [fullRecordGapRow00156_values]

end PrimeFactorUnimodality
