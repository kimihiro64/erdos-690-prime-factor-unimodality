import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00082_values : List Nat :=
  [fullRecordGapCenterValue + 243842,
    fullRecordGapCenterValue + 243926,
    fullRecordGapCenterValue + 243936,
    fullRecordGapCenterValue + 243986,
    fullRecordGapCenterValue + 244058,
    fullRecordGapCenterValue + 244406,
    fullRecordGapCenterValue + 244598,
    fullRecordGapCenterValue + 244646,
    fullRecordGapCenterValue + 244676,
    fullRecordGapCenterValue + 244892,
    fullRecordGapCenterValue + 245222,
    fullRecordGapCenterValue + 245306,
    fullRecordGapCenterValue + 245372,
    fullRecordGapCenterValue + 245438,
    fullRecordGapCenterValue + 245522,
    fullRecordGapCenterValue + 245666,
    fullRecordGapCenterValue + 245852,
    fullRecordGapCenterValue + 245948,
    fullRecordGapCenterValue + 246062,
    fullRecordGapCenterValue + 246212,
    fullRecordGapCenterValue + 246338,
    fullRecordGapCenterValue + 246458,
    fullRecordGapCenterValue + 246548,
    fullRecordGapCenterValue + 246668,
    fullRecordGapCenterValue + 246692,
    fullRecordGapCenterValue + 246878,
    fullRecordGapCenterValue + 246960,
    fullRecordGapCenterValue + 246986,
    fullRecordGapCenterValue + 247238,
    fullRecordGapCenterValue + 247322,
    fullRecordGapCenterValue + 247466,
    fullRecordGapCenterValue + 247658,
    fullRecordGapCenterValue + 247706,
    fullRecordGapCenterValue + 247796,
    fullRecordGapCenterValue + 247808,
    fullRecordGapCenterValue + 247916,
    fullRecordGapCenterValue + 248012,
    fullRecordGapCenterValue + 248306,
    fullRecordGapCenterValue + 248426,
    fullRecordGapCenterValue + 248498,
    fullRecordGapCenterValue + 248582,
    fullRecordGapCenterValue + 248726,
    fullRecordGapCenterValue + 248832,
    fullRecordGapCenterValue + 248876,
    fullRecordGapCenterValue + 248978,
    fullRecordGapCenterValue + 249018,
    fullRecordGapCenterValue + 249266,
    fullRecordGapCenterValue + 249308,
    fullRecordGapCenterValue + 249386,
    fullRecordGapCenterValue + 249638,
    fullRecordGapCenterValue + 249692,
    fullRecordGapCenterValue + 249932,
    fullRecordGapCenterValue + 250028,
    fullRecordGapCenterValue + 250106,
    fullRecordGapCenterValue + 250226,
    fullRecordGapCenterValue + 250238,
    fullRecordGapCenterValue + 250262,
    fullRecordGapCenterValue + 250538,
    fullRecordGapCenterValue + 250622,
    fullRecordGapCenterValue + 250658,
    fullRecordGapCenterValue + 250742,
    fullRecordGapCenterValue + 250748,
    fullRecordGapCenterValue + 250880,
    fullRecordGapCenterValue + 250892]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00082_fermat : ∀ n ∈ fullRecordGapRow00082_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05185_not_prime : ¬(recordGapCenter + 243842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 243842]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05186_not_prime : ¬(recordGapCenter + 243926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 243926]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05187_not_prime : ¬(recordGapCenter + 243936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 243936]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05188_not_prime : ¬(recordGapCenter + 243986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 243986]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05189_not_prime : ¬(recordGapCenter + 244058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 244058]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05190_not_prime : ¬(recordGapCenter + 244406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 244406]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05191_not_prime : ¬(recordGapCenter + 244598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 244598]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05192_not_prime : ¬(recordGapCenter + 244646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 244646]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05193_not_prime : ¬(recordGapCenter + 244676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 244676]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05194_not_prime : ¬(recordGapCenter + 244892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 244892]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05195_not_prime : ¬(recordGapCenter + 245222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 245222]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05196_not_prime : ¬(recordGapCenter + 245306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 245306]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05197_not_prime : ¬(recordGapCenter + 245372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 245372]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05198_not_prime : ¬(recordGapCenter + 245438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 245438]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05199_not_prime : ¬(recordGapCenter + 245522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 245522]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05200_not_prime : ¬(recordGapCenter + 245666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 245666]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05201_not_prime : ¬(recordGapCenter + 245852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 245852]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05202_not_prime : ¬(recordGapCenter + 245948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 245948]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05203_not_prime : ¬(recordGapCenter + 246062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 246062]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05204_not_prime : ¬(recordGapCenter + 246212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 246212]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05205_not_prime : ¬(recordGapCenter + 246338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 246338]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05206_not_prime : ¬(recordGapCenter + 246458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 246458]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05207_not_prime : ¬(recordGapCenter + 246548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 246548]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05208_not_prime : ¬(recordGapCenter + 246668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 246668]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05209_not_prime : ¬(recordGapCenter + 246692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 246692]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05210_not_prime : ¬(recordGapCenter + 246878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 246878]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05211_not_prime : ¬(recordGapCenter + 246960).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 246960]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05212_not_prime : ¬(recordGapCenter + 246986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 246986]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05213_not_prime : ¬(recordGapCenter + 247238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 247238]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05214_not_prime : ¬(recordGapCenter + 247322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 247322]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05215_not_prime : ¬(recordGapCenter + 247466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 247466]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05216_not_prime : ¬(recordGapCenter + 247658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 247658]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05217_not_prime : ¬(recordGapCenter + 247706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 247706]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05218_not_prime : ¬(recordGapCenter + 247796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 247796]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05219_not_prime : ¬(recordGapCenter + 247808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 247808]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05220_not_prime : ¬(recordGapCenter + 247916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 247916]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05221_not_prime : ¬(recordGapCenter + 248012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 248012]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05222_not_prime : ¬(recordGapCenter + 248306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 248306]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05223_not_prime : ¬(recordGapCenter + 248426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 248426]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05224_not_prime : ¬(recordGapCenter + 248498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 248498]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05225_not_prime : ¬(recordGapCenter + 248582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 248582]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05226_not_prime : ¬(recordGapCenter + 248726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 248726]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05227_not_prime : ¬(recordGapCenter + 248832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 248832]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05228_not_prime : ¬(recordGapCenter + 248876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 248876]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05229_not_prime : ¬(recordGapCenter + 248978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 248978]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05230_not_prime : ¬(recordGapCenter + 249018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 249018]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05231_not_prime : ¬(recordGapCenter + 249266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 249266]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05232_not_prime : ¬(recordGapCenter + 249308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 249308]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05233_not_prime : ¬(recordGapCenter + 249386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 249386]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05234_not_prime : ¬(recordGapCenter + 249638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 249638]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05235_not_prime : ¬(recordGapCenter + 249692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 249692]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05236_not_prime : ¬(recordGapCenter + 249932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 249932]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05237_not_prime : ¬(recordGapCenter + 250028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 250028]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05238_not_prime : ¬(recordGapCenter + 250106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 250106]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05239_not_prime : ¬(recordGapCenter + 250226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 250226]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05240_not_prime : ¬(recordGapCenter + 250238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 250238]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05241_not_prime : ¬(recordGapCenter + 250262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 250262]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05242_not_prime : ¬(recordGapCenter + 250538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 250538]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05243_not_prime : ¬(recordGapCenter + 250622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 250622]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05244_not_prime : ¬(recordGapCenter + 250658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 250658]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05245_not_prime : ¬(recordGapCenter + 250742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 250742]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05246_not_prime : ¬(recordGapCenter + 250748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 250748]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05247_not_prime : ¬(recordGapCenter + 250880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 250880]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

theorem fullRecordGapTerm05248_not_prime : ¬(recordGapCenter + 250892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 250892]
  · apply fullRecordGapRow00082_fermat
    simp [fullRecordGapRow00082_values]

end PrimeFactorUnimodality
