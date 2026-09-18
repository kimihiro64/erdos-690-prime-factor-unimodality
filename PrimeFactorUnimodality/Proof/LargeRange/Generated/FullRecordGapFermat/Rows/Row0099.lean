import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00099_values : List Nat :=
  [fullRecordGapCenterValue + 338222,
    fullRecordGapCenterValue + 338262,
    fullRecordGapCenterValue + 338502,
    fullRecordGapCenterValue + 338586,
    fullRecordGapCenterValue + 338612,
    fullRecordGapCenterValue + 338636,
    fullRecordGapCenterValue + 338942,
    fullRecordGapCenterValue + 338948,
    fullRecordGapCenterValue + 338966,
    fullRecordGapCenterValue + 338978,
    fullRecordGapCenterValue + 339006,
    fullRecordGapCenterValue + 339018,
    fullRecordGapCenterValue + 339182,
    fullRecordGapCenterValue + 339186,
    fullRecordGapCenterValue + 339266,
    fullRecordGapCenterValue + 339278,
    fullRecordGapCenterValue + 339428,
    fullRecordGapCenterValue + 339546,
    fullRecordGapCenterValue + 339686,
    fullRecordGapCenterValue + 339798,
    fullRecordGapCenterValue + 339866,
    fullRecordGapCenterValue + 339902,
    fullRecordGapCenterValue + 340026,
    fullRecordGapCenterValue + 340058,
    fullRecordGapCenterValue + 340086,
    fullRecordGapCenterValue + 340148,
    fullRecordGapCenterValue + 340436,
    fullRecordGapCenterValue + 340526,
    fullRecordGapCenterValue + 340698,
    fullRecordGapCenterValue + 340778,
    fullRecordGapCenterValue + 340796,
    fullRecordGapCenterValue + 340946,
    fullRecordGapCenterValue + 340988,
    fullRecordGapCenterValue + 341006,
    fullRecordGapCenterValue + 341036,
    fullRecordGapCenterValue + 341058,
    fullRecordGapCenterValue + 341346,
    fullRecordGapCenterValue + 341378,
    fullRecordGapCenterValue + 341538,
    fullRecordGapCenterValue + 341646,
    fullRecordGapCenterValue + 341708,
    fullRecordGapCenterValue + 341762,
    fullRecordGapCenterValue + 341798,
    fullRecordGapCenterValue + 341906,
    fullRecordGapCenterValue + 341948,
    fullRecordGapCenterValue + 341958,
    fullRecordGapCenterValue + 342086,
    fullRecordGapCenterValue + 342092,
    fullRecordGapCenterValue + 342326,
    fullRecordGapCenterValue + 342462,
    fullRecordGapCenterValue + 342542,
    fullRecordGapCenterValue + 342786,
    fullRecordGapCenterValue + 342806,
    fullRecordGapCenterValue + 342878,
    fullRecordGapCenterValue + 343038,
    fullRecordGapCenterValue + 343058,
    fullRecordGapCenterValue + 343106,
    fullRecordGapCenterValue + 343158,
    fullRecordGapCenterValue + 343166,
    fullRecordGapCenterValue + 343268,
    fullRecordGapCenterValue + 343316,
    fullRecordGapCenterValue + 343446,
    fullRecordGapCenterValue + 343506,
    fullRecordGapCenterValue + 343598]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00099_fermat : ∀ n ∈ fullRecordGapRow00099_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06273_not_prime : ¬(recordGapCenter + 338222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 338222]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06274_not_prime : ¬(recordGapCenter + 338262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 338262]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06275_not_prime : ¬(recordGapCenter + 338502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 338502]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06276_not_prime : ¬(recordGapCenter + 338586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 338586]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06277_not_prime : ¬(recordGapCenter + 338612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 338612]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06278_not_prime : ¬(recordGapCenter + 338636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 338636]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06279_not_prime : ¬(recordGapCenter + 338942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 338942]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06280_not_prime : ¬(recordGapCenter + 338948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 338948]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06281_not_prime : ¬(recordGapCenter + 338966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 338966]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06282_not_prime : ¬(recordGapCenter + 338978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 338978]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06283_not_prime : ¬(recordGapCenter + 339006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 339006]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06284_not_prime : ¬(recordGapCenter + 339018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 339018]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06285_not_prime : ¬(recordGapCenter + 339182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 339182]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06286_not_prime : ¬(recordGapCenter + 339186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 339186]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06287_not_prime : ¬(recordGapCenter + 339266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 339266]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06288_not_prime : ¬(recordGapCenter + 339278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 339278]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06289_not_prime : ¬(recordGapCenter + 339428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 339428]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06290_not_prime : ¬(recordGapCenter + 339546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 339546]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06291_not_prime : ¬(recordGapCenter + 339686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 339686]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06292_not_prime : ¬(recordGapCenter + 339798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 339798]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06293_not_prime : ¬(recordGapCenter + 339866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 339866]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06294_not_prime : ¬(recordGapCenter + 339902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 339902]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06295_not_prime : ¬(recordGapCenter + 340026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 340026]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06296_not_prime : ¬(recordGapCenter + 340058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 340058]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06297_not_prime : ¬(recordGapCenter + 340086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 340086]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06298_not_prime : ¬(recordGapCenter + 340148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 340148]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06299_not_prime : ¬(recordGapCenter + 340436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 340436]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06300_not_prime : ¬(recordGapCenter + 340526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 340526]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06301_not_prime : ¬(recordGapCenter + 340698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 340698]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06302_not_prime : ¬(recordGapCenter + 340778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 340778]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06303_not_prime : ¬(recordGapCenter + 340796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 340796]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06304_not_prime : ¬(recordGapCenter + 340946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 340946]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06305_not_prime : ¬(recordGapCenter + 340988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 340988]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06306_not_prime : ¬(recordGapCenter + 341006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 341006]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06307_not_prime : ¬(recordGapCenter + 341036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 341036]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06308_not_prime : ¬(recordGapCenter + 341058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 341058]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06309_not_prime : ¬(recordGapCenter + 341346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 341346]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06310_not_prime : ¬(recordGapCenter + 341378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 341378]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06311_not_prime : ¬(recordGapCenter + 341538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 341538]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06312_not_prime : ¬(recordGapCenter + 341646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 341646]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06313_not_prime : ¬(recordGapCenter + 341708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 341708]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06314_not_prime : ¬(recordGapCenter + 341762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 341762]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06315_not_prime : ¬(recordGapCenter + 341798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 341798]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06316_not_prime : ¬(recordGapCenter + 341906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 341906]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06317_not_prime : ¬(recordGapCenter + 341948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 341948]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06318_not_prime : ¬(recordGapCenter + 341958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 341958]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06319_not_prime : ¬(recordGapCenter + 342086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 342086]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06320_not_prime : ¬(recordGapCenter + 342092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 342092]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06321_not_prime : ¬(recordGapCenter + 342326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 342326]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06322_not_prime : ¬(recordGapCenter + 342462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 342462]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06323_not_prime : ¬(recordGapCenter + 342542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 342542]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06324_not_prime : ¬(recordGapCenter + 342786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 342786]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06325_not_prime : ¬(recordGapCenter + 342806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 342806]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06326_not_prime : ¬(recordGapCenter + 342878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 342878]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06327_not_prime : ¬(recordGapCenter + 343038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 343038]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06328_not_prime : ¬(recordGapCenter + 343058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 343058]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06329_not_prime : ¬(recordGapCenter + 343106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 343106]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06330_not_prime : ¬(recordGapCenter + 343158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 343158]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06331_not_prime : ¬(recordGapCenter + 343166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 343166]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06332_not_prime : ¬(recordGapCenter + 343268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 343268]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06333_not_prime : ¬(recordGapCenter + 343316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 343316]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06334_not_prime : ¬(recordGapCenter + 343446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 343446]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06335_not_prime : ¬(recordGapCenter + 343506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 343506]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

theorem fullRecordGapTerm06336_not_prime : ¬(recordGapCenter + 343598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 343598]
  · apply fullRecordGapRow00099_fermat
    simp [fullRecordGapRow00099_values]

end PrimeFactorUnimodality
