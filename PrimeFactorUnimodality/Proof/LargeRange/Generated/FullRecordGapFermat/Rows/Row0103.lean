import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00103_values : List Nat :=
  [fullRecordGapCenterValue + 358076,
    fullRecordGapCenterValue + 358082,
    fullRecordGapCenterValue + 358158,
    fullRecordGapCenterValue + 358166,
    fullRecordGapCenterValue + 358286,
    fullRecordGapCenterValue + 358338,
    fullRecordGapCenterValue + 358400,
    fullRecordGapCenterValue + 358412,
    fullRecordGapCenterValue + 358458,
    fullRecordGapCenterValue + 358538,
    fullRecordGapCenterValue + 358562,
    fullRecordGapCenterValue + 358676,
    fullRecordGapCenterValue + 358782,
    fullRecordGapCenterValue + 358922,
    fullRecordGapCenterValue + 359066,
    fullRecordGapCenterValue + 359096,
    fullRecordGapCenterValue + 359186,
    fullRecordGapCenterValue + 359276,
    fullRecordGapCenterValue + 359318,
    fullRecordGapCenterValue + 359342,
    fullRecordGapCenterValue + 359588,
    fullRecordGapCenterValue + 359672,
    fullRecordGapCenterValue + 359846,
    fullRecordGapCenterValue + 359886,
    fullRecordGapCenterValue + 359978,
    fullRecordGapCenterValue + 360056,
    fullRecordGapCenterValue + 360078,
    fullRecordGapCenterValue + 360236,
    fullRecordGapCenterValue + 360362,
    fullRecordGapCenterValue + 360428,
    fullRecordGapCenterValue + 360546,
    fullRecordGapCenterValue + 360596,
    fullRecordGapCenterValue + 360722,
    fullRecordGapCenterValue + 360762,
    fullRecordGapCenterValue + 360782,
    fullRecordGapCenterValue + 360788,
    fullRecordGapCenterValue + 360812,
    fullRecordGapCenterValue + 360908,
    fullRecordGapCenterValue + 361002,
    fullRecordGapCenterValue + 361502,
    fullRecordGapCenterValue + 361506,
    fullRecordGapCenterValue + 361586,
    fullRecordGapCenterValue + 361628,
    fullRecordGapCenterValue + 361898,
    fullRecordGapCenterValue + 361902,
    fullRecordGapCenterValue + 361986,
    fullRecordGapCenterValue + 362078,
    fullRecordGapCenterValue + 362238,
    fullRecordGapCenterValue + 362282,
    fullRecordGapCenterValue + 362486,
    fullRecordGapCenterValue + 362546,
    fullRecordGapCenterValue + 362552,
    fullRecordGapCenterValue + 362588,
    fullRecordGapCenterValue + 362636,
    fullRecordGapCenterValue + 362658,
    fullRecordGapCenterValue + 362708,
    fullRecordGapCenterValue + 362958,
    fullRecordGapCenterValue + 363000,
    fullRecordGapCenterValue + 363002,
    fullRecordGapCenterValue + 363098,
    fullRecordGapCenterValue + 363126,
    fullRecordGapCenterValue + 363338,
    fullRecordGapCenterValue + 363452,
    fullRecordGapCenterValue + 363512]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00103_fermat : ∀ n ∈ fullRecordGapRow00103_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06529_not_prime : ¬(recordGapCenter + 358076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358076]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06530_not_prime : ¬(recordGapCenter + 358082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358082]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06531_not_prime : ¬(recordGapCenter + 358158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358158]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06532_not_prime : ¬(recordGapCenter + 358166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358166]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06533_not_prime : ¬(recordGapCenter + 358286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358286]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06534_not_prime : ¬(recordGapCenter + 358338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358338]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06535_not_prime : ¬(recordGapCenter + 358400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358400]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06536_not_prime : ¬(recordGapCenter + 358412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358412]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06537_not_prime : ¬(recordGapCenter + 358458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358458]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06538_not_prime : ¬(recordGapCenter + 358538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358538]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06539_not_prime : ¬(recordGapCenter + 358562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358562]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06540_not_prime : ¬(recordGapCenter + 358676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358676]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06541_not_prime : ¬(recordGapCenter + 358782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358782]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06542_not_prime : ¬(recordGapCenter + 358922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 358922]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06543_not_prime : ¬(recordGapCenter + 359066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359066]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06544_not_prime : ¬(recordGapCenter + 359096).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359096]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06545_not_prime : ¬(recordGapCenter + 359186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359186]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06546_not_prime : ¬(recordGapCenter + 359276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359276]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06547_not_prime : ¬(recordGapCenter + 359318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359318]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06548_not_prime : ¬(recordGapCenter + 359342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359342]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06549_not_prime : ¬(recordGapCenter + 359588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359588]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06550_not_prime : ¬(recordGapCenter + 359672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359672]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06551_not_prime : ¬(recordGapCenter + 359846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359846]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06552_not_prime : ¬(recordGapCenter + 359886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359886]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06553_not_prime : ¬(recordGapCenter + 359978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 359978]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06554_not_prime : ¬(recordGapCenter + 360056).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360056]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06555_not_prime : ¬(recordGapCenter + 360078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360078]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06556_not_prime : ¬(recordGapCenter + 360236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360236]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06557_not_prime : ¬(recordGapCenter + 360362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360362]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06558_not_prime : ¬(recordGapCenter + 360428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360428]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06559_not_prime : ¬(recordGapCenter + 360546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360546]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06560_not_prime : ¬(recordGapCenter + 360596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360596]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06561_not_prime : ¬(recordGapCenter + 360722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360722]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06562_not_prime : ¬(recordGapCenter + 360762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360762]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06563_not_prime : ¬(recordGapCenter + 360782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360782]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06564_not_prime : ¬(recordGapCenter + 360788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360788]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06565_not_prime : ¬(recordGapCenter + 360812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360812]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06566_not_prime : ¬(recordGapCenter + 360908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 360908]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06567_not_prime : ¬(recordGapCenter + 361002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361002]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06568_not_prime : ¬(recordGapCenter + 361502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361502]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06569_not_prime : ¬(recordGapCenter + 361506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361506]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06570_not_prime : ¬(recordGapCenter + 361586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361586]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06571_not_prime : ¬(recordGapCenter + 361628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361628]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06572_not_prime : ¬(recordGapCenter + 361898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361898]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06573_not_prime : ¬(recordGapCenter + 361902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361902]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06574_not_prime : ¬(recordGapCenter + 361986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 361986]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06575_not_prime : ¬(recordGapCenter + 362078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362078]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06576_not_prime : ¬(recordGapCenter + 362238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362238]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06577_not_prime : ¬(recordGapCenter + 362282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362282]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06578_not_prime : ¬(recordGapCenter + 362486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362486]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06579_not_prime : ¬(recordGapCenter + 362546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362546]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06580_not_prime : ¬(recordGapCenter + 362552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362552]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06581_not_prime : ¬(recordGapCenter + 362588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362588]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06582_not_prime : ¬(recordGapCenter + 362636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362636]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06583_not_prime : ¬(recordGapCenter + 362658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362658]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06584_not_prime : ¬(recordGapCenter + 362708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362708]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06585_not_prime : ¬(recordGapCenter + 362958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 362958]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06586_not_prime : ¬(recordGapCenter + 363000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363000]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06587_not_prime : ¬(recordGapCenter + 363002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363002]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06588_not_prime : ¬(recordGapCenter + 363098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363098]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06589_not_prime : ¬(recordGapCenter + 363126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363126]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06590_not_prime : ¬(recordGapCenter + 363338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363338]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06591_not_prime : ¬(recordGapCenter + 363452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363452]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

theorem fullRecordGapTerm06592_not_prime : ¬(recordGapCenter + 363512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 363512]
  · apply fullRecordGapRow00103_fermat
    simp [fullRecordGapRow00103_values]

end PrimeFactorUnimodality
