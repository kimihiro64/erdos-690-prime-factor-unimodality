import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00163_values : List Nat :=
  [fullRecordGapCenterValue + 625286,
    fullRecordGapCenterValue + 625388,
    fullRecordGapCenterValue + 625398,
    fullRecordGapCenterValue + 625406,
    fullRecordGapCenterValue + 625490,
    fullRecordGapCenterValue + 625598,
    fullRecordGapCenterValue + 625682,
    fullRecordGapCenterValue + 625686,
    fullRecordGapCenterValue + 625832,
    fullRecordGapCenterValue + 625866,
    fullRecordGapCenterValue + 625868,
    fullRecordGapCenterValue + 625910,
    fullRecordGapCenterValue + 625958,
    fullRecordGapCenterValue + 626018,
    fullRecordGapCenterValue + 626162,
    fullRecordGapCenterValue + 626196,
    fullRecordGapCenterValue + 626286,
    fullRecordGapCenterValue + 626298,
    fullRecordGapCenterValue + 626306,
    fullRecordGapCenterValue + 626330,
    fullRecordGapCenterValue + 626390,
    fullRecordGapCenterValue + 626412,
    fullRecordGapCenterValue + 626498,
    fullRecordGapCenterValue + 626636,
    fullRecordGapCenterValue + 626676,
    fullRecordGapCenterValue + 626708,
    fullRecordGapCenterValue + 626822,
    fullRecordGapCenterValue + 626838,
    fullRecordGapCenterValue + 626942,
    fullRecordGapCenterValue + 627086,
    fullRecordGapCenterValue + 627158,
    fullRecordGapCenterValue + 627200,
    fullRecordGapCenterValue + 627258,
    fullRecordGapCenterValue + 627306,
    fullRecordGapCenterValue + 627366,
    fullRecordGapCenterValue + 627468,
    fullRecordGapCenterValue + 627582,
    fullRecordGapCenterValue + 627756,
    fullRecordGapCenterValue + 627758,
    fullRecordGapCenterValue + 627842,
    fullRecordGapCenterValue + 627866,
    fullRecordGapCenterValue + 628076,
    fullRecordGapCenterValue + 628086,
    fullRecordGapCenterValue + 628190,
    fullRecordGapCenterValue + 628302,
    fullRecordGapCenterValue + 628322,
    fullRecordGapCenterValue + 628346,
    fullRecordGapCenterValue + 628412,
    fullRecordGapCenterValue + 628418,
    fullRecordGapCenterValue + 628478,
    fullRecordGapCenterValue + 628526,
    fullRecordGapCenterValue + 628532,
    fullRecordGapCenterValue + 628566,
    fullRecordGapCenterValue + 628568,
    fullRecordGapCenterValue + 628598,
    fullRecordGapCenterValue + 628638,
    fullRecordGapCenterValue + 628652,
    fullRecordGapCenterValue + 628730,
    fullRecordGapCenterValue + 628806,
    fullRecordGapCenterValue + 628818,
    fullRecordGapCenterValue + 628856,
    fullRecordGapCenterValue + 628916,
    fullRecordGapCenterValue + 628982,
    fullRecordGapCenterValue + 628988]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00163_fermat : ∀ n ∈ fullRecordGapRow00163_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10369_not_prime : ¬(recordGapCenter + 625286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625286]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10370_not_prime : ¬(recordGapCenter + 625388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625388]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10371_not_prime : ¬(recordGapCenter + 625398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625398]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10372_not_prime : ¬(recordGapCenter + 625406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625406]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10373_not_prime : ¬(recordGapCenter + 625490).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625490]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10374_not_prime : ¬(recordGapCenter + 625598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625598]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10375_not_prime : ¬(recordGapCenter + 625682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625682]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10376_not_prime : ¬(recordGapCenter + 625686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625686]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10377_not_prime : ¬(recordGapCenter + 625832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625832]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10378_not_prime : ¬(recordGapCenter + 625866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625866]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10379_not_prime : ¬(recordGapCenter + 625868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625868]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10380_not_prime : ¬(recordGapCenter + 625910).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625910]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10381_not_prime : ¬(recordGapCenter + 625958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625958]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10382_not_prime : ¬(recordGapCenter + 626018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626018]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10383_not_prime : ¬(recordGapCenter + 626162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626162]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10384_not_prime : ¬(recordGapCenter + 626196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626196]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10385_not_prime : ¬(recordGapCenter + 626286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626286]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10386_not_prime : ¬(recordGapCenter + 626298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626298]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10387_not_prime : ¬(recordGapCenter + 626306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626306]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10388_not_prime : ¬(recordGapCenter + 626330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626330]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10389_not_prime : ¬(recordGapCenter + 626390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626390]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10390_not_prime : ¬(recordGapCenter + 626412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626412]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10391_not_prime : ¬(recordGapCenter + 626498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626498]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10392_not_prime : ¬(recordGapCenter + 626636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626636]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10393_not_prime : ¬(recordGapCenter + 626676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626676]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10394_not_prime : ¬(recordGapCenter + 626708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626708]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10395_not_prime : ¬(recordGapCenter + 626822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626822]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10396_not_prime : ¬(recordGapCenter + 626838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626838]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10397_not_prime : ¬(recordGapCenter + 626942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 626942]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10398_not_prime : ¬(recordGapCenter + 627086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 627086]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10399_not_prime : ¬(recordGapCenter + 627158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 627158]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10400_not_prime : ¬(recordGapCenter + 627200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 627200]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10401_not_prime : ¬(recordGapCenter + 627258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 627258]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10402_not_prime : ¬(recordGapCenter + 627306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 627306]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10403_not_prime : ¬(recordGapCenter + 627366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 627366]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10404_not_prime : ¬(recordGapCenter + 627468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 627468]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10405_not_prime : ¬(recordGapCenter + 627582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 627582]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10406_not_prime : ¬(recordGapCenter + 627756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 627756]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10407_not_prime : ¬(recordGapCenter + 627758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 627758]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10408_not_prime : ¬(recordGapCenter + 627842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 627842]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10409_not_prime : ¬(recordGapCenter + 627866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 627866]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10410_not_prime : ¬(recordGapCenter + 628076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628076]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10411_not_prime : ¬(recordGapCenter + 628086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628086]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10412_not_prime : ¬(recordGapCenter + 628190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628190]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10413_not_prime : ¬(recordGapCenter + 628302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628302]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10414_not_prime : ¬(recordGapCenter + 628322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628322]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10415_not_prime : ¬(recordGapCenter + 628346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628346]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10416_not_prime : ¬(recordGapCenter + 628412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628412]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10417_not_prime : ¬(recordGapCenter + 628418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628418]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10418_not_prime : ¬(recordGapCenter + 628478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628478]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10419_not_prime : ¬(recordGapCenter + 628526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628526]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10420_not_prime : ¬(recordGapCenter + 628532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628532]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10421_not_prime : ¬(recordGapCenter + 628566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628566]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10422_not_prime : ¬(recordGapCenter + 628568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628568]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10423_not_prime : ¬(recordGapCenter + 628598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628598]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10424_not_prime : ¬(recordGapCenter + 628638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628638]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10425_not_prime : ¬(recordGapCenter + 628652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628652]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10426_not_prime : ¬(recordGapCenter + 628730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628730]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10427_not_prime : ¬(recordGapCenter + 628806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628806]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10428_not_prime : ¬(recordGapCenter + 628818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628818]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10429_not_prime : ¬(recordGapCenter + 628856).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628856]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10430_not_prime : ¬(recordGapCenter + 628916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628916]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10431_not_prime : ¬(recordGapCenter + 628982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628982]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

theorem fullRecordGapTerm10432_not_prime : ¬(recordGapCenter + 628988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 628988]
  · apply fullRecordGapRow00163_fermat
    simp [fullRecordGapRow00163_values]

end PrimeFactorUnimodality
