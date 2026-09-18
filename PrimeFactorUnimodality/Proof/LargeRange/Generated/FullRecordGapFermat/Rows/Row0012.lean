import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00012_values : List Nat :=
  [fullRecordGapCenterValue - 400018,
    fullRecordGapCenterValue - 400012,
    fullRecordGapCenterValue - 399934,
    fullRecordGapCenterValue - 399774,
    fullRecordGapCenterValue - 399628,
    fullRecordGapCenterValue - 399604,
    fullRecordGapCenterValue - 399558,
    fullRecordGapCenterValue - 399508,
    fullRecordGapCenterValue - 399318,
    fullRecordGapCenterValue - 399292,
    fullRecordGapCenterValue - 399198,
    fullRecordGapCenterValue - 399174,
    fullRecordGapCenterValue - 399138,
    fullRecordGapCenterValue - 399054,
    fullRecordGapCenterValue - 398914,
    fullRecordGapCenterValue - 398884,
    fullRecordGapCenterValue - 398758,
    fullRecordGapCenterValue - 398694,
    fullRecordGapCenterValue - 398668,
    fullRecordGapCenterValue - 398572,
    fullRecordGapCenterValue - 398488,
    fullRecordGapCenterValue - 398478,
    fullRecordGapCenterValue - 398362,
    fullRecordGapCenterValue - 398302,
    fullRecordGapCenterValue - 398218,
    fullRecordGapCenterValue - 398092,
    fullRecordGapCenterValue - 398082,
    fullRecordGapCenterValue - 398074,
    fullRecordGapCenterValue - 398058,
    fullRecordGapCenterValue - 397858,
    fullRecordGapCenterValue - 397798,
    fullRecordGapCenterValue - 397758,
    fullRecordGapCenterValue - 397402,
    fullRecordGapCenterValue - 397198,
    fullRecordGapCenterValue - 397108,
    fullRecordGapCenterValue - 396904,
    fullRecordGapCenterValue - 396900,
    fullRecordGapCenterValue - 396892,
    fullRecordGapCenterValue - 396822,
    fullRecordGapCenterValue - 396724,
    fullRecordGapCenterValue - 396562,
    fullRecordGapCenterValue - 396534,
    fullRecordGapCenterValue - 396442,
    fullRecordGapCenterValue - 396412,
    fullRecordGapCenterValue - 396174,
    fullRecordGapCenterValue - 395842,
    fullRecordGapCenterValue - 395818,
    fullRecordGapCenterValue - 395644,
    fullRecordGapCenterValue - 395574,
    fullRecordGapCenterValue - 395464,
    fullRecordGapCenterValue - 395394,
    fullRecordGapCenterValue - 395202,
    fullRecordGapCenterValue - 395134,
    fullRecordGapCenterValue - 395022,
    fullRecordGapCenterValue - 394734,
    fullRecordGapCenterValue - 394678,
    fullRecordGapCenterValue - 394558,
    fullRecordGapCenterValue - 394522,
    fullRecordGapCenterValue - 394314,
    fullRecordGapCenterValue - 394294,
    fullRecordGapCenterValue - 394242,
    fullRecordGapCenterValue - 394194,
    fullRecordGapCenterValue - 394018,
    fullRecordGapCenterValue - 393942]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00012_fermat : ∀ n ∈ fullRecordGapRow00012_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00705_not_prime : ¬(recordGapCenter - 400018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400018]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00706_not_prime : ¬(recordGapCenter - 400012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 400012]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00707_not_prime : ¬(recordGapCenter - 399934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399934]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00708_not_prime : ¬(recordGapCenter - 399774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399774]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00709_not_prime : ¬(recordGapCenter - 399628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399628]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00710_not_prime : ¬(recordGapCenter - 399604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399604]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00711_not_prime : ¬(recordGapCenter - 399558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399558]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00712_not_prime : ¬(recordGapCenter - 399508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399508]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00713_not_prime : ¬(recordGapCenter - 399318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399318]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00714_not_prime : ¬(recordGapCenter - 399292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399292]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00715_not_prime : ¬(recordGapCenter - 399198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399198]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00716_not_prime : ¬(recordGapCenter - 399174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399174]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00717_not_prime : ¬(recordGapCenter - 399138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399138]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00718_not_prime : ¬(recordGapCenter - 399054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 399054]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00719_not_prime : ¬(recordGapCenter - 398914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398914]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00720_not_prime : ¬(recordGapCenter - 398884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398884]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00721_not_prime : ¬(recordGapCenter - 398758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398758]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00722_not_prime : ¬(recordGapCenter - 398694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398694]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00723_not_prime : ¬(recordGapCenter - 398668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398668]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00724_not_prime : ¬(recordGapCenter - 398572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398572]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00725_not_prime : ¬(recordGapCenter - 398488).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398488]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00726_not_prime : ¬(recordGapCenter - 398478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398478]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00727_not_prime : ¬(recordGapCenter - 398362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398362]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00728_not_prime : ¬(recordGapCenter - 398302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398302]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00729_not_prime : ¬(recordGapCenter - 398218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398218]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00730_not_prime : ¬(recordGapCenter - 398092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398092]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00731_not_prime : ¬(recordGapCenter - 398082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398082]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00732_not_prime : ¬(recordGapCenter - 398074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398074]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00733_not_prime : ¬(recordGapCenter - 398058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 398058]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00734_not_prime : ¬(recordGapCenter - 397858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 397858]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00735_not_prime : ¬(recordGapCenter - 397798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 397798]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00736_not_prime : ¬(recordGapCenter - 397758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 397758]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00737_not_prime : ¬(recordGapCenter - 397402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 397402]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00738_not_prime : ¬(recordGapCenter - 397198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 397198]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00739_not_prime : ¬(recordGapCenter - 397108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 397108]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00740_not_prime : ¬(recordGapCenter - 396904).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396904]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00741_not_prime : ¬(recordGapCenter - 396900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396900]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00742_not_prime : ¬(recordGapCenter - 396892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396892]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00743_not_prime : ¬(recordGapCenter - 396822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396822]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00744_not_prime : ¬(recordGapCenter - 396724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396724]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00745_not_prime : ¬(recordGapCenter - 396562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396562]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00746_not_prime : ¬(recordGapCenter - 396534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396534]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00747_not_prime : ¬(recordGapCenter - 396442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396442]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00748_not_prime : ¬(recordGapCenter - 396412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396412]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00749_not_prime : ¬(recordGapCenter - 396174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 396174]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00750_not_prime : ¬(recordGapCenter - 395842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395842]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00751_not_prime : ¬(recordGapCenter - 395818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395818]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00752_not_prime : ¬(recordGapCenter - 395644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395644]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00753_not_prime : ¬(recordGapCenter - 395574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395574]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00754_not_prime : ¬(recordGapCenter - 395464).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395464]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00755_not_prime : ¬(recordGapCenter - 395394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395394]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00756_not_prime : ¬(recordGapCenter - 395202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395202]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00757_not_prime : ¬(recordGapCenter - 395134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395134]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00758_not_prime : ¬(recordGapCenter - 395022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 395022]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00759_not_prime : ¬(recordGapCenter - 394734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394734]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00760_not_prime : ¬(recordGapCenter - 394678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394678]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00761_not_prime : ¬(recordGapCenter - 394558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394558]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00762_not_prime : ¬(recordGapCenter - 394522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394522]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00763_not_prime : ¬(recordGapCenter - 394314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394314]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00764_not_prime : ¬(recordGapCenter - 394294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394294]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00765_not_prime : ¬(recordGapCenter - 394242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394242]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00766_not_prime : ¬(recordGapCenter - 394194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394194]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00767_not_prime : ¬(recordGapCenter - 394018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 394018]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

theorem fullRecordGapTerm00768_not_prime : ¬(recordGapCenter - 393942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 393942]
  · apply fullRecordGapRow00012_fermat
    simp [fullRecordGapRow00012_values]

end PrimeFactorUnimodality
