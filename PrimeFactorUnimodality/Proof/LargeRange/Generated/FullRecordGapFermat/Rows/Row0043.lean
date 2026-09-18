import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00043_values : List Nat :=
  [fullRecordGapCenterValue - 220828,
    fullRecordGapCenterValue - 220678,
    fullRecordGapCenterValue - 220468,
    fullRecordGapCenterValue - 220138,
    fullRecordGapCenterValue - 220084,
    fullRecordGapCenterValue - 220078,
    fullRecordGapCenterValue - 220000,
    fullRecordGapCenterValue - 219874,
    fullRecordGapCenterValue - 219694,
    fullRecordGapCenterValue - 219658,
    fullRecordGapCenterValue - 219508,
    fullRecordGapCenterValue - 219238,
    fullRecordGapCenterValue - 219148,
    fullRecordGapCenterValue - 219034,
    fullRecordGapCenterValue - 219004,
    fullRecordGapCenterValue - 218908,
    fullRecordGapCenterValue - 218700,
    fullRecordGapCenterValue - 218668,
    fullRecordGapCenterValue - 218458,
    fullRecordGapCenterValue - 218404,
    fullRecordGapCenterValue - 218308,
    fullRecordGapCenterValue - 218242,
    fullRecordGapCenterValue - 218188,
    fullRecordGapCenterValue - 217942,
    fullRecordGapCenterValue - 217774,
    fullRecordGapCenterValue - 217762,
    fullRecordGapCenterValue - 217654,
    fullRecordGapCenterValue - 217468,
    fullRecordGapCenterValue - 217354,
    fullRecordGapCenterValue - 217324,
    fullRecordGapCenterValue - 217174,
    fullRecordGapCenterValue - 217114,
    fullRecordGapCenterValue - 217108,
    fullRecordGapCenterValue - 216922,
    fullRecordGapCenterValue - 216772,
    fullRecordGapCenterValue - 216382,
    fullRecordGapCenterValue - 216358,
    fullRecordGapCenterValue - 216262,
    fullRecordGapCenterValue - 216214,
    fullRecordGapCenterValue - 216090,
    fullRecordGapCenterValue - 216082,
    fullRecordGapCenterValue - 216052,
    fullRecordGapCenterValue - 216004,
    fullRecordGapCenterValue - 215854,
    fullRecordGapCenterValue - 215794,
    fullRecordGapCenterValue - 215674,
    fullRecordGapCenterValue - 215668,
    fullRecordGapCenterValue - 215554,
    fullRecordGapCenterValue - 215374,
    fullRecordGapCenterValue - 214924,
    fullRecordGapCenterValue - 214678,
    fullRecordGapCenterValue - 214612,
    fullRecordGapCenterValue - 214492,
    fullRecordGapCenterValue - 214342,
    fullRecordGapCenterValue - 214114,
    fullRecordGapCenterValue - 213814,
    fullRecordGapCenterValue - 213748,
    fullRecordGapCenterValue - 213628,
    fullRecordGapCenterValue - 213574,
    fullRecordGapCenterValue - 213562,
    fullRecordGapCenterValue - 213444,
    fullRecordGapCenterValue - 213442,
    fullRecordGapCenterValue - 213412,
    fullRecordGapCenterValue - 213292]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00043_fermat : ∀ n ∈ fullRecordGapRow00043_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02689_not_prime : ¬(recordGapCenter - 220828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220828]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02690_not_prime : ¬(recordGapCenter - 220678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220678]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02691_not_prime : ¬(recordGapCenter - 220468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220468]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02692_not_prime : ¬(recordGapCenter - 220138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220138]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02693_not_prime : ¬(recordGapCenter - 220084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220084]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02694_not_prime : ¬(recordGapCenter - 220078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220078]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02695_not_prime : ¬(recordGapCenter - 220000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220000]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02696_not_prime : ¬(recordGapCenter - 219874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219874]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02697_not_prime : ¬(recordGapCenter - 219694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219694]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02698_not_prime : ¬(recordGapCenter - 219658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219658]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02699_not_prime : ¬(recordGapCenter - 219508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219508]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02700_not_prime : ¬(recordGapCenter - 219238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219238]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02701_not_prime : ¬(recordGapCenter - 219148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219148]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02702_not_prime : ¬(recordGapCenter - 219034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219034]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02703_not_prime : ¬(recordGapCenter - 219004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219004]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02704_not_prime : ¬(recordGapCenter - 218908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218908]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02705_not_prime : ¬(recordGapCenter - 218700).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218700]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02706_not_prime : ¬(recordGapCenter - 218668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218668]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02707_not_prime : ¬(recordGapCenter - 218458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218458]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02708_not_prime : ¬(recordGapCenter - 218404).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218404]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02709_not_prime : ¬(recordGapCenter - 218308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218308]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02710_not_prime : ¬(recordGapCenter - 218242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218242]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02711_not_prime : ¬(recordGapCenter - 218188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218188]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02712_not_prime : ¬(recordGapCenter - 217942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217942]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02713_not_prime : ¬(recordGapCenter - 217774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217774]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02714_not_prime : ¬(recordGapCenter - 217762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217762]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02715_not_prime : ¬(recordGapCenter - 217654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217654]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02716_not_prime : ¬(recordGapCenter - 217468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217468]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02717_not_prime : ¬(recordGapCenter - 217354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217354]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02718_not_prime : ¬(recordGapCenter - 217324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217324]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02719_not_prime : ¬(recordGapCenter - 217174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217174]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02720_not_prime : ¬(recordGapCenter - 217114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217114]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02721_not_prime : ¬(recordGapCenter - 217108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217108]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02722_not_prime : ¬(recordGapCenter - 216922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216922]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02723_not_prime : ¬(recordGapCenter - 216772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216772]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02724_not_prime : ¬(recordGapCenter - 216382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216382]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02725_not_prime : ¬(recordGapCenter - 216358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216358]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02726_not_prime : ¬(recordGapCenter - 216262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216262]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02727_not_prime : ¬(recordGapCenter - 216214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216214]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02728_not_prime : ¬(recordGapCenter - 216090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216090]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02729_not_prime : ¬(recordGapCenter - 216082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216082]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02730_not_prime : ¬(recordGapCenter - 216052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216052]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02731_not_prime : ¬(recordGapCenter - 216004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216004]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02732_not_prime : ¬(recordGapCenter - 215854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 215854]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02733_not_prime : ¬(recordGapCenter - 215794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 215794]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02734_not_prime : ¬(recordGapCenter - 215674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 215674]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02735_not_prime : ¬(recordGapCenter - 215668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 215668]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02736_not_prime : ¬(recordGapCenter - 215554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 215554]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02737_not_prime : ¬(recordGapCenter - 215374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 215374]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02738_not_prime : ¬(recordGapCenter - 214924).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 214924]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02739_not_prime : ¬(recordGapCenter - 214678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 214678]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02740_not_prime : ¬(recordGapCenter - 214612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 214612]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02741_not_prime : ¬(recordGapCenter - 214492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 214492]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02742_not_prime : ¬(recordGapCenter - 214342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 214342]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02743_not_prime : ¬(recordGapCenter - 214114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 214114]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02744_not_prime : ¬(recordGapCenter - 213814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213814]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02745_not_prime : ¬(recordGapCenter - 213748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213748]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02746_not_prime : ¬(recordGapCenter - 213628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213628]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02747_not_prime : ¬(recordGapCenter - 213574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213574]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02748_not_prime : ¬(recordGapCenter - 213562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213562]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02749_not_prime : ¬(recordGapCenter - 213444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213444]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02750_not_prime : ¬(recordGapCenter - 213442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213442]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02751_not_prime : ¬(recordGapCenter - 213412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213412]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

theorem fullRecordGapTerm02752_not_prime : ¬(recordGapCenter - 213292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213292]
  · apply fullRecordGapRow00043_fermat
    simp [fullRecordGapRow00043_values]

end PrimeFactorUnimodality
