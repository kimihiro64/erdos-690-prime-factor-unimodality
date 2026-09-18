import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00090_values : List Nat :=
  [fullRecordGapCenterValue + 291246,
    fullRecordGapCenterValue + 291426,
    fullRecordGapCenterValue + 291638,
    fullRecordGapCenterValue + 291692,
    fullRecordGapCenterValue + 291722,
    fullRecordGapCenterValue + 291882,
    fullRecordGapCenterValue + 291908,
    fullRecordGapCenterValue + 292062,
    fullRecordGapCenterValue + 292118,
    fullRecordGapCenterValue + 292386,
    fullRecordGapCenterValue + 292506,
    fullRecordGapCenterValue + 292532,
    fullRecordGapCenterValue + 292566,
    fullRecordGapCenterValue + 292598,
    fullRecordGapCenterValue + 292602,
    fullRecordGapCenterValue + 292686,
    fullRecordGapCenterValue + 292722,
    fullRecordGapCenterValue + 292766,
    fullRecordGapCenterValue + 292820,
    fullRecordGapCenterValue + 292898,
    fullRecordGapCenterValue + 292902,
    fullRecordGapCenterValue + 292938,
    fullRecordGapCenterValue + 293042,
    fullRecordGapCenterValue + 293108,
    fullRecordGapCenterValue + 293126,
    fullRecordGapCenterValue + 293162,
    fullRecordGapCenterValue + 293442,
    fullRecordGapCenterValue + 293682,
    fullRecordGapCenterValue + 293732,
    fullRecordGapCenterValue + 293786,
    fullRecordGapCenterValue + 293946,
    fullRecordGapCenterValue + 294018,
    fullRecordGapCenterValue + 294030,
    fullRecordGapCenterValue + 294212,
    fullRecordGapCenterValue + 294222,
    fullRecordGapCenterValue + 294326,
    fullRecordGapCenterValue + 294332,
    fullRecordGapCenterValue + 294458,
    fullRecordGapCenterValue + 294486,
    fullRecordGapCenterValue + 294506,
    fullRecordGapCenterValue + 294578,
    fullRecordGapCenterValue + 294618,
    fullRecordGapCenterValue + 294638,
    fullRecordGapCenterValue + 294702,
    fullRecordGapCenterValue + 294726,
    fullRecordGapCenterValue + 294836,
    fullRecordGapCenterValue + 294908,
    fullRecordGapCenterValue + 294942,
    fullRecordGapCenterValue + 294962,
    fullRecordGapCenterValue + 295158,
    fullRecordGapCenterValue + 295166,
    fullRecordGapCenterValue + 295206,
    fullRecordGapCenterValue + 295292,
    fullRecordGapCenterValue + 295418,
    fullRecordGapCenterValue + 295586,
    fullRecordGapCenterValue + 295598,
    fullRecordGapCenterValue + 295622,
    fullRecordGapCenterValue + 295662,
    fullRecordGapCenterValue + 295680,
    fullRecordGapCenterValue + 295706,
    fullRecordGapCenterValue + 295838,
    fullRecordGapCenterValue + 295842,
    fullRecordGapCenterValue + 295892,
    fullRecordGapCenterValue + 295898]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00090_fermat : ∀ n ∈ fullRecordGapRow00090_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05697_not_prime : ¬(recordGapCenter + 291246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 291246]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05698_not_prime : ¬(recordGapCenter + 291426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 291426]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05699_not_prime : ¬(recordGapCenter + 291638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 291638]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05700_not_prime : ¬(recordGapCenter + 291692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 291692]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05701_not_prime : ¬(recordGapCenter + 291722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 291722]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05702_not_prime : ¬(recordGapCenter + 291882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 291882]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05703_not_prime : ¬(recordGapCenter + 291908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 291908]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05704_not_prime : ¬(recordGapCenter + 292062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292062]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05705_not_prime : ¬(recordGapCenter + 292118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292118]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05706_not_prime : ¬(recordGapCenter + 292386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292386]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05707_not_prime : ¬(recordGapCenter + 292506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292506]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05708_not_prime : ¬(recordGapCenter + 292532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292532]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05709_not_prime : ¬(recordGapCenter + 292566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292566]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05710_not_prime : ¬(recordGapCenter + 292598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292598]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05711_not_prime : ¬(recordGapCenter + 292602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292602]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05712_not_prime : ¬(recordGapCenter + 292686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292686]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05713_not_prime : ¬(recordGapCenter + 292722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292722]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05714_not_prime : ¬(recordGapCenter + 292766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292766]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05715_not_prime : ¬(recordGapCenter + 292820).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292820]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05716_not_prime : ¬(recordGapCenter + 292898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292898]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05717_not_prime : ¬(recordGapCenter + 292902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292902]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05718_not_prime : ¬(recordGapCenter + 292938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 292938]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05719_not_prime : ¬(recordGapCenter + 293042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 293042]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05720_not_prime : ¬(recordGapCenter + 293108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 293108]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05721_not_prime : ¬(recordGapCenter + 293126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 293126]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05722_not_prime : ¬(recordGapCenter + 293162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 293162]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05723_not_prime : ¬(recordGapCenter + 293442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 293442]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05724_not_prime : ¬(recordGapCenter + 293682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 293682]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05725_not_prime : ¬(recordGapCenter + 293732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 293732]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05726_not_prime : ¬(recordGapCenter + 293786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 293786]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05727_not_prime : ¬(recordGapCenter + 293946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 293946]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05728_not_prime : ¬(recordGapCenter + 294018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294018]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05729_not_prime : ¬(recordGapCenter + 294030).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294030]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05730_not_prime : ¬(recordGapCenter + 294212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294212]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05731_not_prime : ¬(recordGapCenter + 294222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294222]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05732_not_prime : ¬(recordGapCenter + 294326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294326]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05733_not_prime : ¬(recordGapCenter + 294332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294332]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05734_not_prime : ¬(recordGapCenter + 294458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294458]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05735_not_prime : ¬(recordGapCenter + 294486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294486]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05736_not_prime : ¬(recordGapCenter + 294506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294506]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05737_not_prime : ¬(recordGapCenter + 294578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294578]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05738_not_prime : ¬(recordGapCenter + 294618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294618]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05739_not_prime : ¬(recordGapCenter + 294638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294638]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05740_not_prime : ¬(recordGapCenter + 294702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294702]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05741_not_prime : ¬(recordGapCenter + 294726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294726]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05742_not_prime : ¬(recordGapCenter + 294836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294836]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05743_not_prime : ¬(recordGapCenter + 294908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294908]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05744_not_prime : ¬(recordGapCenter + 294942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294942]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05745_not_prime : ¬(recordGapCenter + 294962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 294962]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05746_not_prime : ¬(recordGapCenter + 295158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295158]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05747_not_prime : ¬(recordGapCenter + 295166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295166]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05748_not_prime : ¬(recordGapCenter + 295206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295206]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05749_not_prime : ¬(recordGapCenter + 295292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295292]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05750_not_prime : ¬(recordGapCenter + 295418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295418]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05751_not_prime : ¬(recordGapCenter + 295586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295586]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05752_not_prime : ¬(recordGapCenter + 295598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295598]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05753_not_prime : ¬(recordGapCenter + 295622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295622]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05754_not_prime : ¬(recordGapCenter + 295662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295662]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05755_not_prime : ¬(recordGapCenter + 295680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295680]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05756_not_prime : ¬(recordGapCenter + 295706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295706]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05757_not_prime : ¬(recordGapCenter + 295838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295838]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05758_not_prime : ¬(recordGapCenter + 295842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295842]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05759_not_prime : ¬(recordGapCenter + 295892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295892]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

theorem fullRecordGapTerm05760_not_prime : ¬(recordGapCenter + 295898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 295898]
  · apply fullRecordGapRow00090_fermat
    simp [fullRecordGapRow00090_values]

end PrimeFactorUnimodality
