import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00115_values : List Nat :=
  [fullRecordGapCenterValue + 418142,
    fullRecordGapCenterValue + 418146,
    fullRecordGapCenterValue + 418316,
    fullRecordGapCenterValue + 418346,
    fullRecordGapCenterValue + 418406,
    fullRecordGapCenterValue + 418422,
    fullRecordGapCenterValue + 418442,
    fullRecordGapCenterValue + 418556,
    fullRecordGapCenterValue + 418566,
    fullRecordGapCenterValue + 418602,
    fullRecordGapCenterValue + 418742,
    fullRecordGapCenterValue + 418868,
    fullRecordGapCenterValue + 418892,
    fullRecordGapCenterValue + 418926,
    fullRecordGapCenterValue + 419246,
    fullRecordGapCenterValue + 419318,
    fullRecordGapCenterValue + 419402,
    fullRecordGapCenterValue + 419438,
    fullRecordGapCenterValue + 419466,
    fullRecordGapCenterValue + 419486,
    fullRecordGapCenterValue + 419618,
    fullRecordGapCenterValue + 419702,
    fullRecordGapCenterValue + 419858,
    fullRecordGapCenterValue + 419906,
    fullRecordGapCenterValue + 419912,
    fullRecordGapCenterValue + 419948,
    fullRecordGapCenterValue + 419996,
    fullRecordGapCenterValue + 420000,
    fullRecordGapCenterValue + 420008,
    fullRecordGapCenterValue + 420338,
    fullRecordGapCenterValue + 420386,
    fullRecordGapCenterValue + 420638,
    fullRecordGapCenterValue + 420726,
    fullRecordGapCenterValue + 420738,
    fullRecordGapCenterValue + 420842,
    fullRecordGapCenterValue + 420956,
    fullRecordGapCenterValue + 420962,
    fullRecordGapCenterValue + 420978,
    fullRecordGapCenterValue + 421202,
    fullRecordGapCenterValue + 421262,
    fullRecordGapCenterValue + 421338,
    fullRecordGapCenterValue + 421418,
    fullRecordGapCenterValue + 421422,
    fullRecordGapCenterValue + 421622,
    fullRecordGapCenterValue + 421646,
    fullRecordGapCenterValue + 421688,
    fullRecordGapCenterValue + 421706,
    fullRecordGapCenterValue + 421796,
    fullRecordGapCenterValue + 421962,
    fullRecordGapCenterValue + 422102,
    fullRecordGapCenterValue + 422108,
    fullRecordGapCenterValue + 422126,
    fullRecordGapCenterValue + 422252,
    fullRecordGapCenterValue + 422258,
    fullRecordGapCenterValue + 422306,
    fullRecordGapCenterValue + 422538,
    fullRecordGapCenterValue + 422576,
    fullRecordGapCenterValue + 422678,
    fullRecordGapCenterValue + 422696,
    fullRecordGapCenterValue + 422732,
    fullRecordGapCenterValue + 422738,
    fullRecordGapCenterValue + 422886,
    fullRecordGapCenterValue + 422888,
    fullRecordGapCenterValue + 422922]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00115_fermat : ∀ n ∈ fullRecordGapRow00115_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07297_not_prime : ¬(recordGapCenter + 418142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418142]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07298_not_prime : ¬(recordGapCenter + 418146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418146]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07299_not_prime : ¬(recordGapCenter + 418316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418316]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07300_not_prime : ¬(recordGapCenter + 418346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418346]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07301_not_prime : ¬(recordGapCenter + 418406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418406]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07302_not_prime : ¬(recordGapCenter + 418422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418422]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07303_not_prime : ¬(recordGapCenter + 418442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418442]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07304_not_prime : ¬(recordGapCenter + 418556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418556]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07305_not_prime : ¬(recordGapCenter + 418566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418566]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07306_not_prime : ¬(recordGapCenter + 418602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418602]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07307_not_prime : ¬(recordGapCenter + 418742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418742]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07308_not_prime : ¬(recordGapCenter + 418868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418868]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07309_not_prime : ¬(recordGapCenter + 418892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418892]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07310_not_prime : ¬(recordGapCenter + 418926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418926]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07311_not_prime : ¬(recordGapCenter + 419246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 419246]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07312_not_prime : ¬(recordGapCenter + 419318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 419318]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07313_not_prime : ¬(recordGapCenter + 419402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 419402]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07314_not_prime : ¬(recordGapCenter + 419438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 419438]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07315_not_prime : ¬(recordGapCenter + 419466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 419466]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07316_not_prime : ¬(recordGapCenter + 419486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 419486]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07317_not_prime : ¬(recordGapCenter + 419618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 419618]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07318_not_prime : ¬(recordGapCenter + 419702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 419702]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07319_not_prime : ¬(recordGapCenter + 419858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 419858]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07320_not_prime : ¬(recordGapCenter + 419906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 419906]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07321_not_prime : ¬(recordGapCenter + 419912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 419912]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07322_not_prime : ¬(recordGapCenter + 419948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 419948]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07323_not_prime : ¬(recordGapCenter + 419996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 419996]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07324_not_prime : ¬(recordGapCenter + 420000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 420000]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07325_not_prime : ¬(recordGapCenter + 420008).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 420008]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07326_not_prime : ¬(recordGapCenter + 420338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 420338]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07327_not_prime : ¬(recordGapCenter + 420386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 420386]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07328_not_prime : ¬(recordGapCenter + 420638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 420638]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07329_not_prime : ¬(recordGapCenter + 420726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 420726]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07330_not_prime : ¬(recordGapCenter + 420738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 420738]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07331_not_prime : ¬(recordGapCenter + 420842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 420842]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07332_not_prime : ¬(recordGapCenter + 420956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 420956]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07333_not_prime : ¬(recordGapCenter + 420962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 420962]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07334_not_prime : ¬(recordGapCenter + 420978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 420978]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07335_not_prime : ¬(recordGapCenter + 421202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 421202]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07336_not_prime : ¬(recordGapCenter + 421262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 421262]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07337_not_prime : ¬(recordGapCenter + 421338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 421338]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07338_not_prime : ¬(recordGapCenter + 421418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 421418]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07339_not_prime : ¬(recordGapCenter + 421422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 421422]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07340_not_prime : ¬(recordGapCenter + 421622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 421622]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07341_not_prime : ¬(recordGapCenter + 421646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 421646]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07342_not_prime : ¬(recordGapCenter + 421688).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 421688]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07343_not_prime : ¬(recordGapCenter + 421706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 421706]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07344_not_prime : ¬(recordGapCenter + 421796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 421796]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07345_not_prime : ¬(recordGapCenter + 421962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 421962]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07346_not_prime : ¬(recordGapCenter + 422102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422102]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07347_not_prime : ¬(recordGapCenter + 422108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422108]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07348_not_prime : ¬(recordGapCenter + 422126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422126]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07349_not_prime : ¬(recordGapCenter + 422252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422252]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07350_not_prime : ¬(recordGapCenter + 422258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422258]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07351_not_prime : ¬(recordGapCenter + 422306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422306]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07352_not_prime : ¬(recordGapCenter + 422538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422538]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07353_not_prime : ¬(recordGapCenter + 422576).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422576]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07354_not_prime : ¬(recordGapCenter + 422678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422678]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07355_not_prime : ¬(recordGapCenter + 422696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422696]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07356_not_prime : ¬(recordGapCenter + 422732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422732]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07357_not_prime : ¬(recordGapCenter + 422738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422738]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07358_not_prime : ¬(recordGapCenter + 422886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422886]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07359_not_prime : ¬(recordGapCenter + 422888).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422888]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

theorem fullRecordGapTerm07360_not_prime : ¬(recordGapCenter + 422922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 422922]
  · apply fullRecordGapRow00115_fermat
    simp [fullRecordGapRow00115_values]

end PrimeFactorUnimodality
