import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00027_values : List Nat :=
  [fullRecordGapCenterValue - 323322,
    fullRecordGapCenterValue - 323278,
    fullRecordGapCenterValue - 323094,
    fullRecordGapCenterValue - 322948,
    fullRecordGapCenterValue - 322914,
    fullRecordGapCenterValue - 322732,
    fullRecordGapCenterValue - 322698,
    fullRecordGapCenterValue - 322618,
    fullRecordGapCenterValue - 322534,
    fullRecordGapCenterValue - 322444,
    fullRecordGapCenterValue - 322402,
    fullRecordGapCenterValue - 322314,
    fullRecordGapCenterValue - 322228,
    fullRecordGapCenterValue - 321942,
    fullRecordGapCenterValue - 321702,
    fullRecordGapCenterValue - 321654,
    fullRecordGapCenterValue - 321634,
    fullRecordGapCenterValue - 321562,
    fullRecordGapCenterValue - 321558,
    fullRecordGapCenterValue - 321502,
    fullRecordGapCenterValue - 321478,
    fullRecordGapCenterValue - 321418,
    fullRecordGapCenterValue - 321394,
    fullRecordGapCenterValue - 321388,
    fullRecordGapCenterValue - 321274,
    fullRecordGapCenterValue - 321004,
    fullRecordGapCenterValue - 320932,
    fullRecordGapCenterValue - 320884,
    fullRecordGapCenterValue - 320668,
    fullRecordGapCenterValue - 320442,
    fullRecordGapCenterValue - 320308,
    fullRecordGapCenterValue - 320284,
    fullRecordGapCenterValue - 320262,
    fullRecordGapCenterValue - 320154,
    fullRecordGapCenterValue - 320098,
    fullRecordGapCenterValue - 319954,
    fullRecordGapCenterValue - 319938,
    fullRecordGapCenterValue - 319798,
    fullRecordGapCenterValue - 319582,
    fullRecordGapCenterValue - 319492,
    fullRecordGapCenterValue - 319402,
    fullRecordGapCenterValue - 319342,
    fullRecordGapCenterValue - 319234,
    fullRecordGapCenterValue - 319204,
    fullRecordGapCenterValue - 319108,
    fullRecordGapCenterValue - 318814,
    fullRecordGapCenterValue - 318778,
    fullRecordGapCenterValue - 318462,
    fullRecordGapCenterValue - 318414,
    fullRecordGapCenterValue - 318334,
    fullRecordGapCenterValue - 318244,
    fullRecordGapCenterValue - 318148,
    fullRecordGapCenterValue - 318034,
    fullRecordGapCenterValue - 317994,
    fullRecordGapCenterValue - 317818,
    fullRecordGapCenterValue - 317802,
    fullRecordGapCenterValue - 317554,
    fullRecordGapCenterValue - 317274,
    fullRecordGapCenterValue - 317154,
    fullRecordGapCenterValue - 317022,
    fullRecordGapCenterValue - 316978,
    fullRecordGapCenterValue - 316902,
    fullRecordGapCenterValue - 316858,
    fullRecordGapCenterValue - 316714]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00027_fermat : ∀ n ∈ fullRecordGapRow00027_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01665_not_prime : ¬(recordGapCenter - 323322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323322]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01666_not_prime : ¬(recordGapCenter - 323278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323278]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01667_not_prime : ¬(recordGapCenter - 323094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323094]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01668_not_prime : ¬(recordGapCenter - 322948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322948]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01669_not_prime : ¬(recordGapCenter - 322914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322914]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01670_not_prime : ¬(recordGapCenter - 322732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322732]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01671_not_prime : ¬(recordGapCenter - 322698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322698]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01672_not_prime : ¬(recordGapCenter - 322618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322618]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01673_not_prime : ¬(recordGapCenter - 322534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322534]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01674_not_prime : ¬(recordGapCenter - 322444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322444]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01675_not_prime : ¬(recordGapCenter - 322402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322402]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01676_not_prime : ¬(recordGapCenter - 322314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322314]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01677_not_prime : ¬(recordGapCenter - 322228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 322228]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01678_not_prime : ¬(recordGapCenter - 321942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321942]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01679_not_prime : ¬(recordGapCenter - 321702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321702]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01680_not_prime : ¬(recordGapCenter - 321654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321654]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01681_not_prime : ¬(recordGapCenter - 321634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321634]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01682_not_prime : ¬(recordGapCenter - 321562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321562]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01683_not_prime : ¬(recordGapCenter - 321558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321558]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01684_not_prime : ¬(recordGapCenter - 321502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321502]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01685_not_prime : ¬(recordGapCenter - 321478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321478]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01686_not_prime : ¬(recordGapCenter - 321418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321418]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01687_not_prime : ¬(recordGapCenter - 321394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321394]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01688_not_prime : ¬(recordGapCenter - 321388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321388]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01689_not_prime : ¬(recordGapCenter - 321274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321274]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01690_not_prime : ¬(recordGapCenter - 321004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 321004]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01691_not_prime : ¬(recordGapCenter - 320932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320932]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01692_not_prime : ¬(recordGapCenter - 320884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320884]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01693_not_prime : ¬(recordGapCenter - 320668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320668]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01694_not_prime : ¬(recordGapCenter - 320442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320442]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01695_not_prime : ¬(recordGapCenter - 320308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320308]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01696_not_prime : ¬(recordGapCenter - 320284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320284]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01697_not_prime : ¬(recordGapCenter - 320262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320262]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01698_not_prime : ¬(recordGapCenter - 320154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320154]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01699_not_prime : ¬(recordGapCenter - 320098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 320098]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01700_not_prime : ¬(recordGapCenter - 319954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319954]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01701_not_prime : ¬(recordGapCenter - 319938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319938]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01702_not_prime : ¬(recordGapCenter - 319798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319798]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01703_not_prime : ¬(recordGapCenter - 319582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319582]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01704_not_prime : ¬(recordGapCenter - 319492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319492]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01705_not_prime : ¬(recordGapCenter - 319402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319402]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01706_not_prime : ¬(recordGapCenter - 319342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319342]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01707_not_prime : ¬(recordGapCenter - 319234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319234]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01708_not_prime : ¬(recordGapCenter - 319204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319204]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01709_not_prime : ¬(recordGapCenter - 319108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 319108]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01710_not_prime : ¬(recordGapCenter - 318814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318814]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01711_not_prime : ¬(recordGapCenter - 318778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318778]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01712_not_prime : ¬(recordGapCenter - 318462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318462]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01713_not_prime : ¬(recordGapCenter - 318414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318414]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01714_not_prime : ¬(recordGapCenter - 318334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318334]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01715_not_prime : ¬(recordGapCenter - 318244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318244]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01716_not_prime : ¬(recordGapCenter - 318148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318148]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01717_not_prime : ¬(recordGapCenter - 318034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 318034]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01718_not_prime : ¬(recordGapCenter - 317994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 317994]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01719_not_prime : ¬(recordGapCenter - 317818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 317818]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01720_not_prime : ¬(recordGapCenter - 317802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 317802]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01721_not_prime : ¬(recordGapCenter - 317554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 317554]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01722_not_prime : ¬(recordGapCenter - 317274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 317274]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01723_not_prime : ¬(recordGapCenter - 317154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 317154]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01724_not_prime : ¬(recordGapCenter - 317022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 317022]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01725_not_prime : ¬(recordGapCenter - 316978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316978]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01726_not_prime : ¬(recordGapCenter - 316902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316902]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01727_not_prime : ¬(recordGapCenter - 316858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316858]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

theorem fullRecordGapTerm01728_not_prime : ¬(recordGapCenter - 316714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 316714]
  · apply fullRecordGapRow00027_fermat
    simp [fullRecordGapRow00027_values]

end PrimeFactorUnimodality
