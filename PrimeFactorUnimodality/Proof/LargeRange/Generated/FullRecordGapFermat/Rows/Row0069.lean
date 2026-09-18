import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00069_values : List Nat :=
  [fullRecordGapCenterValue + 134822,
    fullRecordGapCenterValue + 134906,
    fullRecordGapCenterValue + 135000,
    fullRecordGapCenterValue + 135158,
    fullRecordGapCenterValue + 135398,
    fullRecordGapCenterValue + 135446,
    fullRecordGapCenterValue + 135602,
    fullRecordGapCenterValue + 135828,
    fullRecordGapCenterValue + 135986,
    fullRecordGapCenterValue + 136080,
    fullRecordGapCenterValue + 136082,
    fullRecordGapCenterValue + 136118,
    fullRecordGapCenterValue + 136622,
    fullRecordGapCenterValue + 136778,
    fullRecordGapCenterValue + 136886,
    fullRecordGapCenterValue + 137366,
    fullRecordGapCenterValue + 137426,
    fullRecordGapCenterValue + 137498,
    fullRecordGapCenterValue + 137582,
    fullRecordGapCenterValue + 137798,
    fullRecordGapCenterValue + 138122,
    fullRecordGapCenterValue + 138146,
    fullRecordGapCenterValue + 138240,
    fullRecordGapCenterValue + 138302,
    fullRecordGapCenterValue + 138386,
    fullRecordGapCenterValue + 138518,
    fullRecordGapCenterValue + 138600,
    fullRecordGapCenterValue + 138806,
    fullRecordGapCenterValue + 138986,
    fullRecordGapCenterValue + 139382,
    fullRecordGapCenterValue + 139478,
    fullRecordGapCenterValue + 139526,
    fullRecordGapCenterValue + 139658,
    fullRecordGapCenterValue + 139862,
    fullRecordGapCenterValue + 140018,
    fullRecordGapCenterValue + 140078,
    fullRecordGapCenterValue + 140102,
    fullRecordGapCenterValue + 140198,
    fullRecordGapCenterValue + 140222,
    fullRecordGapCenterValue + 140282,
    fullRecordGapCenterValue + 140702,
    fullRecordGapCenterValue + 140918,
    fullRecordGapCenterValue + 141278,
    fullRecordGapCenterValue + 141458,
    fullRecordGapCenterValue + 141758,
    fullRecordGapCenterValue + 141842,
    fullRecordGapCenterValue + 141998,
    fullRecordGapCenterValue + 142178,
    fullRecordGapCenterValue + 142296,
    fullRecordGapCenterValue + 142322,
    fullRecordGapCenterValue + 142418,
    fullRecordGapCenterValue + 142560,
    fullRecordGapCenterValue + 142838,
    fullRecordGapCenterValue + 142958,
    fullRecordGapCenterValue + 143342,
    fullRecordGapCenterValue + 143360,
    fullRecordGapCenterValue + 143748,
    fullRecordGapCenterValue + 144000,
    fullRecordGapCenterValue + 144062,
    fullRecordGapCenterValue + 144182,
    fullRecordGapCenterValue + 144218,
    fullRecordGapCenterValue + 144446,
    fullRecordGapCenterValue + 144506,
    fullRecordGapCenterValue + 144842]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00069_fermat : ∀ n ∈ fullRecordGapRow00069_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04353_not_prime : ¬(recordGapCenter + 134822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 134822]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04354_not_prime : ¬(recordGapCenter + 134906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 134906]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04355_not_prime : ¬(recordGapCenter + 135000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 135000]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04356_not_prime : ¬(recordGapCenter + 135158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 135158]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04357_not_prime : ¬(recordGapCenter + 135398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 135398]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04358_not_prime : ¬(recordGapCenter + 135446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 135446]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04359_not_prime : ¬(recordGapCenter + 135602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 135602]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04360_not_prime : ¬(recordGapCenter + 135828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 135828]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04361_not_prime : ¬(recordGapCenter + 135986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 135986]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04362_not_prime : ¬(recordGapCenter + 136080).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 136080]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04363_not_prime : ¬(recordGapCenter + 136082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 136082]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04364_not_prime : ¬(recordGapCenter + 136118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 136118]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04365_not_prime : ¬(recordGapCenter + 136622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 136622]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04366_not_prime : ¬(recordGapCenter + 136778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 136778]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04367_not_prime : ¬(recordGapCenter + 136886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 136886]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04368_not_prime : ¬(recordGapCenter + 137366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 137366]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04369_not_prime : ¬(recordGapCenter + 137426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 137426]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04370_not_prime : ¬(recordGapCenter + 137498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 137498]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04371_not_prime : ¬(recordGapCenter + 137582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 137582]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04372_not_prime : ¬(recordGapCenter + 137798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 137798]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04373_not_prime : ¬(recordGapCenter + 138122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138122]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04374_not_prime : ¬(recordGapCenter + 138146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138146]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04375_not_prime : ¬(recordGapCenter + 138240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138240]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04376_not_prime : ¬(recordGapCenter + 138302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138302]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04377_not_prime : ¬(recordGapCenter + 138386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138386]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04378_not_prime : ¬(recordGapCenter + 138518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138518]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04379_not_prime : ¬(recordGapCenter + 138600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138600]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04380_not_prime : ¬(recordGapCenter + 138806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138806]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04381_not_prime : ¬(recordGapCenter + 138986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 138986]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04382_not_prime : ¬(recordGapCenter + 139382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 139382]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04383_not_prime : ¬(recordGapCenter + 139478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 139478]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04384_not_prime : ¬(recordGapCenter + 139526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 139526]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04385_not_prime : ¬(recordGapCenter + 139658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 139658]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04386_not_prime : ¬(recordGapCenter + 139862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 139862]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04387_not_prime : ¬(recordGapCenter + 140018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140018]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04388_not_prime : ¬(recordGapCenter + 140078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140078]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04389_not_prime : ¬(recordGapCenter + 140102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140102]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04390_not_prime : ¬(recordGapCenter + 140198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140198]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04391_not_prime : ¬(recordGapCenter + 140222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140222]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04392_not_prime : ¬(recordGapCenter + 140282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140282]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04393_not_prime : ¬(recordGapCenter + 140702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140702]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04394_not_prime : ¬(recordGapCenter + 140918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 140918]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04395_not_prime : ¬(recordGapCenter + 141278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 141278]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04396_not_prime : ¬(recordGapCenter + 141458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 141458]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04397_not_prime : ¬(recordGapCenter + 141758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 141758]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04398_not_prime : ¬(recordGapCenter + 141842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 141842]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04399_not_prime : ¬(recordGapCenter + 141998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 141998]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04400_not_prime : ¬(recordGapCenter + 142178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 142178]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04401_not_prime : ¬(recordGapCenter + 142296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 142296]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04402_not_prime : ¬(recordGapCenter + 142322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 142322]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04403_not_prime : ¬(recordGapCenter + 142418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 142418]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04404_not_prime : ¬(recordGapCenter + 142560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 142560]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04405_not_prime : ¬(recordGapCenter + 142838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 142838]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04406_not_prime : ¬(recordGapCenter + 142958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 142958]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04407_not_prime : ¬(recordGapCenter + 143342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 143342]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04408_not_prime : ¬(recordGapCenter + 143360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 143360]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04409_not_prime : ¬(recordGapCenter + 143748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 143748]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04410_not_prime : ¬(recordGapCenter + 144000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144000]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04411_not_prime : ¬(recordGapCenter + 144062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144062]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04412_not_prime : ¬(recordGapCenter + 144182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144182]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04413_not_prime : ¬(recordGapCenter + 144218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144218]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04414_not_prime : ¬(recordGapCenter + 144446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144446]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04415_not_prime : ¬(recordGapCenter + 144506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144506]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

theorem fullRecordGapTerm04416_not_prime : ¬(recordGapCenter + 144842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144842]
  · apply fullRecordGapRow00069_fermat
    simp [fullRecordGapRow00069_values]

end PrimeFactorUnimodality
