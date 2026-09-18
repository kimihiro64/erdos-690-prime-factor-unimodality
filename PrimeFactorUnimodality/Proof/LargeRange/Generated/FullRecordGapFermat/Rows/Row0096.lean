import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00096_values : List Nat :=
  [fullRecordGapCenterValue + 322106,
    fullRecordGapCenterValue + 322148,
    fullRecordGapCenterValue + 322158,
    fullRecordGapCenterValue + 322268,
    fullRecordGapCenterValue + 322386,
    fullRecordGapCenterValue + 322442,
    fullRecordGapCenterValue + 322466,
    fullRecordGapCenterValue + 322526,
    fullRecordGapCenterValue + 322638,
    fullRecordGapCenterValue + 322662,
    fullRecordGapCenterValue + 322988,
    fullRecordGapCenterValue + 323006,
    fullRecordGapCenterValue + 323108,
    fullRecordGapCenterValue + 323156,
    fullRecordGapCenterValue + 323282,
    fullRecordGapCenterValue + 323346,
    fullRecordGapCenterValue + 323486,
    fullRecordGapCenterValue + 323522,
    fullRecordGapCenterValue + 323538,
    fullRecordGapCenterValue + 323558,
    fullRecordGapCenterValue + 323636,
    fullRecordGapCenterValue + 323678,
    fullRecordGapCenterValue + 323706,
    fullRecordGapCenterValue + 323762,
    fullRecordGapCenterValue + 323846,
    fullRecordGapCenterValue + 323852,
    fullRecordGapCenterValue + 323942,
    fullRecordGapCenterValue + 323958,
    fullRecordGapCenterValue + 324000,
    fullRecordGapCenterValue + 324182,
    fullRecordGapCenterValue + 324222,
    fullRecordGapCenterValue + 324308,
    fullRecordGapCenterValue + 324332,
    fullRecordGapCenterValue + 324476,
    fullRecordGapCenterValue + 324546,
    fullRecordGapCenterValue + 324686,
    fullRecordGapCenterValue + 324692,
    fullRecordGapCenterValue + 324726,
    fullRecordGapCenterValue + 324788,
    fullRecordGapCenterValue + 324878,
    fullRecordGapCenterValue + 324902,
    fullRecordGapCenterValue + 324906,
    fullRecordGapCenterValue + 324956,
    fullRecordGapCenterValue + 325106,
    fullRecordGapCenterValue + 325196,
    fullRecordGapCenterValue + 325298,
    fullRecordGapCenterValue + 325302,
    fullRecordGapCenterValue + 325382,
    fullRecordGapCenterValue + 325406,
    fullRecordGapCenterValue + 325502,
    fullRecordGapCenterValue + 325718,
    fullRecordGapCenterValue + 325778,
    fullRecordGapCenterValue + 325946,
    fullRecordGapCenterValue + 325986,
    fullRecordGapCenterValue + 326202,
    fullRecordGapCenterValue + 326226,
    fullRecordGapCenterValue + 326258,
    fullRecordGapCenterValue + 326406,
    fullRecordGapCenterValue + 326526,
    fullRecordGapCenterValue + 326592,
    fullRecordGapCenterValue + 326700,
    fullRecordGapCenterValue + 326726,
    fullRecordGapCenterValue + 326996,
    fullRecordGapCenterValue + 327122]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00096_fermat : ∀ n ∈ fullRecordGapRow00096_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06081_not_prime : ¬(recordGapCenter + 322106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 322106]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06082_not_prime : ¬(recordGapCenter + 322148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 322148]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06083_not_prime : ¬(recordGapCenter + 322158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 322158]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06084_not_prime : ¬(recordGapCenter + 322268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 322268]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06085_not_prime : ¬(recordGapCenter + 322386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 322386]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06086_not_prime : ¬(recordGapCenter + 322442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 322442]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06087_not_prime : ¬(recordGapCenter + 322466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 322466]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06088_not_prime : ¬(recordGapCenter + 322526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 322526]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06089_not_prime : ¬(recordGapCenter + 322638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 322638]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06090_not_prime : ¬(recordGapCenter + 322662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 322662]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06091_not_prime : ¬(recordGapCenter + 322988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 322988]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06092_not_prime : ¬(recordGapCenter + 323006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323006]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06093_not_prime : ¬(recordGapCenter + 323108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323108]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06094_not_prime : ¬(recordGapCenter + 323156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323156]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06095_not_prime : ¬(recordGapCenter + 323282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323282]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06096_not_prime : ¬(recordGapCenter + 323346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323346]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06097_not_prime : ¬(recordGapCenter + 323486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323486]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06098_not_prime : ¬(recordGapCenter + 323522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323522]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06099_not_prime : ¬(recordGapCenter + 323538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323538]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06100_not_prime : ¬(recordGapCenter + 323558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323558]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06101_not_prime : ¬(recordGapCenter + 323636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323636]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06102_not_prime : ¬(recordGapCenter + 323678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323678]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06103_not_prime : ¬(recordGapCenter + 323706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323706]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06104_not_prime : ¬(recordGapCenter + 323762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323762]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06105_not_prime : ¬(recordGapCenter + 323846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323846]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06106_not_prime : ¬(recordGapCenter + 323852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323852]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06107_not_prime : ¬(recordGapCenter + 323942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323942]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06108_not_prime : ¬(recordGapCenter + 323958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 323958]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06109_not_prime : ¬(recordGapCenter + 324000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324000]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06110_not_prime : ¬(recordGapCenter + 324182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324182]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06111_not_prime : ¬(recordGapCenter + 324222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324222]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06112_not_prime : ¬(recordGapCenter + 324308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324308]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06113_not_prime : ¬(recordGapCenter + 324332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324332]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06114_not_prime : ¬(recordGapCenter + 324476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324476]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06115_not_prime : ¬(recordGapCenter + 324546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324546]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06116_not_prime : ¬(recordGapCenter + 324686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324686]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06117_not_prime : ¬(recordGapCenter + 324692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324692]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06118_not_prime : ¬(recordGapCenter + 324726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324726]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06119_not_prime : ¬(recordGapCenter + 324788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324788]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06120_not_prime : ¬(recordGapCenter + 324878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324878]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06121_not_prime : ¬(recordGapCenter + 324902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324902]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06122_not_prime : ¬(recordGapCenter + 324906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324906]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06123_not_prime : ¬(recordGapCenter + 324956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 324956]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06124_not_prime : ¬(recordGapCenter + 325106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 325106]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06125_not_prime : ¬(recordGapCenter + 325196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 325196]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06126_not_prime : ¬(recordGapCenter + 325298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 325298]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06127_not_prime : ¬(recordGapCenter + 325302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 325302]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06128_not_prime : ¬(recordGapCenter + 325382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 325382]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06129_not_prime : ¬(recordGapCenter + 325406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 325406]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06130_not_prime : ¬(recordGapCenter + 325502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 325502]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06131_not_prime : ¬(recordGapCenter + 325718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 325718]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06132_not_prime : ¬(recordGapCenter + 325778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 325778]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06133_not_prime : ¬(recordGapCenter + 325946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 325946]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06134_not_prime : ¬(recordGapCenter + 325986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 325986]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06135_not_prime : ¬(recordGapCenter + 326202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 326202]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06136_not_prime : ¬(recordGapCenter + 326226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 326226]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06137_not_prime : ¬(recordGapCenter + 326258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 326258]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06138_not_prime : ¬(recordGapCenter + 326406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 326406]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06139_not_prime : ¬(recordGapCenter + 326526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 326526]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06140_not_prime : ¬(recordGapCenter + 326592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 326592]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06141_not_prime : ¬(recordGapCenter + 326700).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 326700]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06142_not_prime : ¬(recordGapCenter + 326726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 326726]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06143_not_prime : ¬(recordGapCenter + 326996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 326996]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

theorem fullRecordGapTerm06144_not_prime : ¬(recordGapCenter + 327122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 327122]
  · apply fullRecordGapRow00096_fermat
    simp [fullRecordGapRow00096_values]

end PrimeFactorUnimodality
