import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00091_values : List Nat :=
  [fullRecordGapCenterValue + 296108,
    fullRecordGapCenterValue + 296346,
    fullRecordGapCenterValue + 296466,
    fullRecordGapCenterValue + 296502,
    fullRecordGapCenterValue + 296558,
    fullRecordGapCenterValue + 296598,
    fullRecordGapCenterValue + 296636,
    fullRecordGapCenterValue + 296678,
    fullRecordGapCenterValue + 296762,
    fullRecordGapCenterValue + 296822,
    fullRecordGapCenterValue + 296858,
    fullRecordGapCenterValue + 296942,
    fullRecordGapCenterValue + 297026,
    fullRecordGapCenterValue + 297098,
    fullRecordGapCenterValue + 297138,
    fullRecordGapCenterValue + 297188,
    fullRecordGapCenterValue + 297218,
    fullRecordGapCenterValue + 297386,
    fullRecordGapCenterValue + 297452,
    fullRecordGapCenterValue + 297566,
    fullRecordGapCenterValue + 297582,
    fullRecordGapCenterValue + 297746,
    fullRecordGapCenterValue + 297798,
    fullRecordGapCenterValue + 297866,
    fullRecordGapCenterValue + 297978,
    fullRecordGapCenterValue + 298022,
    fullRecordGapCenterValue + 298106,
    fullRecordGapCenterValue + 298182,
    fullRecordGapCenterValue + 298226,
    fullRecordGapCenterValue + 298292,
    fullRecordGapCenterValue + 298502,
    fullRecordGapCenterValue + 298538,
    fullRecordGapCenterValue + 298698,
    fullRecordGapCenterValue + 298748,
    fullRecordGapCenterValue + 298796,
    fullRecordGapCenterValue + 298838,
    fullRecordGapCenterValue + 298842,
    fullRecordGapCenterValue + 298916,
    fullRecordGapCenterValue + 298986,
    fullRecordGapCenterValue + 299036,
    fullRecordGapCenterValue + 299058,
    fullRecordGapCenterValue + 299066,
    fullRecordGapCenterValue + 299376,
    fullRecordGapCenterValue + 299378,
    fullRecordGapCenterValue + 299462,
    fullRecordGapCenterValue + 299492,
    fullRecordGapCenterValue + 299498,
    fullRecordGapCenterValue + 299622,
    fullRecordGapCenterValue + 299678,
    fullRecordGapCenterValue + 299742,
    fullRecordGapCenterValue + 299822,
    fullRecordGapCenterValue + 299906,
    fullRecordGapCenterValue + 299958,
    fullRecordGapCenterValue + 300000,
    fullRecordGapCenterValue + 300116,
    fullRecordGapCenterValue + 300126,
    fullRecordGapCenterValue + 300198,
    fullRecordGapCenterValue + 300332,
    fullRecordGapCenterValue + 300338,
    fullRecordGapCenterValue + 300386,
    fullRecordGapCenterValue + 300522,
    fullRecordGapCenterValue + 300602,
    fullRecordGapCenterValue + 300878,
    fullRecordGapCenterValue + 301046]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00091_fermat : ∀ n ∈ fullRecordGapRow00091_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05761_not_prime : ¬(recordGapCenter + 296108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 296108]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05762_not_prime : ¬(recordGapCenter + 296346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 296346]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05763_not_prime : ¬(recordGapCenter + 296466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 296466]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05764_not_prime : ¬(recordGapCenter + 296502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 296502]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05765_not_prime : ¬(recordGapCenter + 296558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 296558]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05766_not_prime : ¬(recordGapCenter + 296598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 296598]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05767_not_prime : ¬(recordGapCenter + 296636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 296636]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05768_not_prime : ¬(recordGapCenter + 296678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 296678]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05769_not_prime : ¬(recordGapCenter + 296762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 296762]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05770_not_prime : ¬(recordGapCenter + 296822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 296822]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05771_not_prime : ¬(recordGapCenter + 296858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 296858]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05772_not_prime : ¬(recordGapCenter + 296942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 296942]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05773_not_prime : ¬(recordGapCenter + 297026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 297026]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05774_not_prime : ¬(recordGapCenter + 297098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 297098]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05775_not_prime : ¬(recordGapCenter + 297138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 297138]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05776_not_prime : ¬(recordGapCenter + 297188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 297188]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05777_not_prime : ¬(recordGapCenter + 297218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 297218]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05778_not_prime : ¬(recordGapCenter + 297386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 297386]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05779_not_prime : ¬(recordGapCenter + 297452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 297452]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05780_not_prime : ¬(recordGapCenter + 297566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 297566]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05781_not_prime : ¬(recordGapCenter + 297582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 297582]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05782_not_prime : ¬(recordGapCenter + 297746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 297746]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05783_not_prime : ¬(recordGapCenter + 297798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 297798]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05784_not_prime : ¬(recordGapCenter + 297866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 297866]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05785_not_prime : ¬(recordGapCenter + 297978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 297978]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05786_not_prime : ¬(recordGapCenter + 298022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 298022]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05787_not_prime : ¬(recordGapCenter + 298106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 298106]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05788_not_prime : ¬(recordGapCenter + 298182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 298182]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05789_not_prime : ¬(recordGapCenter + 298226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 298226]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05790_not_prime : ¬(recordGapCenter + 298292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 298292]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05791_not_prime : ¬(recordGapCenter + 298502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 298502]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05792_not_prime : ¬(recordGapCenter + 298538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 298538]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05793_not_prime : ¬(recordGapCenter + 298698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 298698]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05794_not_prime : ¬(recordGapCenter + 298748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 298748]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05795_not_prime : ¬(recordGapCenter + 298796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 298796]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05796_not_prime : ¬(recordGapCenter + 298838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 298838]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05797_not_prime : ¬(recordGapCenter + 298842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 298842]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05798_not_prime : ¬(recordGapCenter + 298916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 298916]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05799_not_prime : ¬(recordGapCenter + 298986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 298986]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05800_not_prime : ¬(recordGapCenter + 299036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 299036]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05801_not_prime : ¬(recordGapCenter + 299058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 299058]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05802_not_prime : ¬(recordGapCenter + 299066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 299066]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05803_not_prime : ¬(recordGapCenter + 299376).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 299376]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05804_not_prime : ¬(recordGapCenter + 299378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 299378]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05805_not_prime : ¬(recordGapCenter + 299462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 299462]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05806_not_prime : ¬(recordGapCenter + 299492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 299492]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05807_not_prime : ¬(recordGapCenter + 299498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 299498]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05808_not_prime : ¬(recordGapCenter + 299622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 299622]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05809_not_prime : ¬(recordGapCenter + 299678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 299678]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05810_not_prime : ¬(recordGapCenter + 299742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 299742]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05811_not_prime : ¬(recordGapCenter + 299822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 299822]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05812_not_prime : ¬(recordGapCenter + 299906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 299906]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05813_not_prime : ¬(recordGapCenter + 299958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 299958]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05814_not_prime : ¬(recordGapCenter + 300000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 300000]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05815_not_prime : ¬(recordGapCenter + 300116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 300116]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05816_not_prime : ¬(recordGapCenter + 300126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 300126]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05817_not_prime : ¬(recordGapCenter + 300198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 300198]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05818_not_prime : ¬(recordGapCenter + 300332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 300332]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05819_not_prime : ¬(recordGapCenter + 300338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 300338]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05820_not_prime : ¬(recordGapCenter + 300386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 300386]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05821_not_prime : ¬(recordGapCenter + 300522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 300522]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05822_not_prime : ¬(recordGapCenter + 300602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 300602]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05823_not_prime : ¬(recordGapCenter + 300878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 300878]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

theorem fullRecordGapTerm05824_not_prime : ¬(recordGapCenter + 301046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 301046]
  · apply fullRecordGapRow00091_fermat
    simp [fullRecordGapRow00091_values]

end PrimeFactorUnimodality
