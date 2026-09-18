import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00166_values : List Nat :=
  [fullRecordGapCenterValue + 637382,
    fullRecordGapCenterValue + 637430,
    fullRecordGapCenterValue + 637458,
    fullRecordGapCenterValue + 637548,
    fullRecordGapCenterValue + 637610,
    fullRecordGapCenterValue + 637646,
    fullRecordGapCenterValue + 637682,
    fullRecordGapCenterValue + 637742,
    fullRecordGapCenterValue + 637766,
    fullRecordGapCenterValue + 637788,
    fullRecordGapCenterValue + 637926,
    fullRecordGapCenterValue + 638090,
    fullRecordGapCenterValue + 638178,
    fullRecordGapCenterValue + 638186,
    fullRecordGapCenterValue + 638246,
    fullRecordGapCenterValue + 638382,
    fullRecordGapCenterValue + 638412,
    fullRecordGapCenterValue + 638466,
    fullRecordGapCenterValue + 638468,
    fullRecordGapCenterValue + 638516,
    fullRecordGapCenterValue + 638562,
    fullRecordGapCenterValue + 638582,
    fullRecordGapCenterValue + 638598,
    fullRecordGapCenterValue + 638772,
    fullRecordGapCenterValue + 638880,
    fullRecordGapCenterValue + 638888,
    fullRecordGapCenterValue + 638906,
    fullRecordGapCenterValue + 638936,
    fullRecordGapCenterValue + 638948,
    fullRecordGapCenterValue + 639038,
    fullRecordGapCenterValue + 639278,
    fullRecordGapCenterValue + 639332,
    fullRecordGapCenterValue + 639348,
    fullRecordGapCenterValue + 639362,
    fullRecordGapCenterValue + 639458,
    fullRecordGapCenterValue + 639546,
    fullRecordGapCenterValue + 639588,
    fullRecordGapCenterValue + 639758,
    fullRecordGapCenterValue + 639942,
    fullRecordGapCenterValue + 639986,
    fullRecordGapCenterValue + 640070,
    fullRecordGapCenterValue + 640076,
    fullRecordGapCenterValue + 640106,
    fullRecordGapCenterValue + 640308,
    fullRecordGapCenterValue + 640316,
    fullRecordGapCenterValue + 640332,
    fullRecordGapCenterValue + 640362,
    fullRecordGapCenterValue + 640418,
    fullRecordGapCenterValue + 640572,
    fullRecordGapCenterValue + 640652,
    fullRecordGapCenterValue + 640682,
    fullRecordGapCenterValue + 640806,
    fullRecordGapCenterValue + 640862,
    fullRecordGapCenterValue + 640868,
    fullRecordGapCenterValue + 640938,
    fullRecordGapCenterValue + 641028,
    fullRecordGapCenterValue + 641042,
    fullRecordGapCenterValue + 641090,
    fullRecordGapCenterValue + 641126,
    fullRecordGapCenterValue + 641166,
    fullRecordGapCenterValue + 641202,
    fullRecordGapCenterValue + 641222,
    fullRecordGapCenterValue + 641226,
    fullRecordGapCenterValue + 641372]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00166_fermat : ∀ n ∈ fullRecordGapRow00166_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10561_not_prime : ¬(recordGapCenter + 637382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637382]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10562_not_prime : ¬(recordGapCenter + 637430).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637430]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10563_not_prime : ¬(recordGapCenter + 637458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637458]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10564_not_prime : ¬(recordGapCenter + 637548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637548]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10565_not_prime : ¬(recordGapCenter + 637610).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637610]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10566_not_prime : ¬(recordGapCenter + 637646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637646]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10567_not_prime : ¬(recordGapCenter + 637682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637682]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10568_not_prime : ¬(recordGapCenter + 637742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637742]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10569_not_prime : ¬(recordGapCenter + 637766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637766]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10570_not_prime : ¬(recordGapCenter + 637788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637788]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10571_not_prime : ¬(recordGapCenter + 637926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 637926]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10572_not_prime : ¬(recordGapCenter + 638090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638090]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10573_not_prime : ¬(recordGapCenter + 638178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638178]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10574_not_prime : ¬(recordGapCenter + 638186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638186]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10575_not_prime : ¬(recordGapCenter + 638246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638246]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10576_not_prime : ¬(recordGapCenter + 638382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638382]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10577_not_prime : ¬(recordGapCenter + 638412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638412]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10578_not_prime : ¬(recordGapCenter + 638466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638466]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10579_not_prime : ¬(recordGapCenter + 638468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638468]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10580_not_prime : ¬(recordGapCenter + 638516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638516]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10581_not_prime : ¬(recordGapCenter + 638562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638562]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10582_not_prime : ¬(recordGapCenter + 638582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638582]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10583_not_prime : ¬(recordGapCenter + 638598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638598]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10584_not_prime : ¬(recordGapCenter + 638772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638772]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10585_not_prime : ¬(recordGapCenter + 638880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638880]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10586_not_prime : ¬(recordGapCenter + 638888).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638888]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10587_not_prime : ¬(recordGapCenter + 638906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638906]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10588_not_prime : ¬(recordGapCenter + 638936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638936]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10589_not_prime : ¬(recordGapCenter + 638948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 638948]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10590_not_prime : ¬(recordGapCenter + 639038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639038]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10591_not_prime : ¬(recordGapCenter + 639278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639278]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10592_not_prime : ¬(recordGapCenter + 639332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639332]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10593_not_prime : ¬(recordGapCenter + 639348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639348]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10594_not_prime : ¬(recordGapCenter + 639362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639362]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10595_not_prime : ¬(recordGapCenter + 639458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639458]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10596_not_prime : ¬(recordGapCenter + 639546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639546]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10597_not_prime : ¬(recordGapCenter + 639588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639588]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10598_not_prime : ¬(recordGapCenter + 639758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639758]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10599_not_prime : ¬(recordGapCenter + 639942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639942]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10600_not_prime : ¬(recordGapCenter + 639986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 639986]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10601_not_prime : ¬(recordGapCenter + 640070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640070]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10602_not_prime : ¬(recordGapCenter + 640076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640076]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10603_not_prime : ¬(recordGapCenter + 640106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640106]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10604_not_prime : ¬(recordGapCenter + 640308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640308]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10605_not_prime : ¬(recordGapCenter + 640316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640316]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10606_not_prime : ¬(recordGapCenter + 640332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640332]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10607_not_prime : ¬(recordGapCenter + 640362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640362]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10608_not_prime : ¬(recordGapCenter + 640418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640418]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10609_not_prime : ¬(recordGapCenter + 640572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640572]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10610_not_prime : ¬(recordGapCenter + 640652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640652]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10611_not_prime : ¬(recordGapCenter + 640682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640682]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10612_not_prime : ¬(recordGapCenter + 640806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640806]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10613_not_prime : ¬(recordGapCenter + 640862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640862]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10614_not_prime : ¬(recordGapCenter + 640868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640868]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10615_not_prime : ¬(recordGapCenter + 640938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 640938]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10616_not_prime : ¬(recordGapCenter + 641028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641028]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10617_not_prime : ¬(recordGapCenter + 641042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641042]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10618_not_prime : ¬(recordGapCenter + 641090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641090]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10619_not_prime : ¬(recordGapCenter + 641126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641126]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10620_not_prime : ¬(recordGapCenter + 641166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641166]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10621_not_prime : ¬(recordGapCenter + 641202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641202]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10622_not_prime : ¬(recordGapCenter + 641222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641222]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10623_not_prime : ¬(recordGapCenter + 641226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641226]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

theorem fullRecordGapTerm10624_not_prime : ¬(recordGapCenter + 641372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641372]
  · apply fullRecordGapRow00166_fermat
    simp [fullRecordGapRow00166_values]

end PrimeFactorUnimodality
