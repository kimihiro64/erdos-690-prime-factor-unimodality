import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00132_values : List Nat :=
  [fullRecordGapCenterValue + 497066,
    fullRecordGapCenterValue + 497298,
    fullRecordGapCenterValue + 497348,
    fullRecordGapCenterValue + 497390,
    fullRecordGapCenterValue + 497418,
    fullRecordGapCenterValue + 497498,
    fullRecordGapCenterValue + 497732,
    fullRecordGapCenterValue + 497738,
    fullRecordGapCenterValue + 497786,
    fullRecordGapCenterValue + 497870,
    fullRecordGapCenterValue + 498036,
    fullRecordGapCenterValue + 498282,
    fullRecordGapCenterValue + 498398,
    fullRecordGapCenterValue + 498558,
    fullRecordGapCenterValue + 498572,
    fullRecordGapCenterValue + 498702,
    fullRecordGapCenterValue + 498716,
    fullRecordGapCenterValue + 498776,
    fullRecordGapCenterValue + 498842,
    fullRecordGapCenterValue + 498878,
    fullRecordGapCenterValue + 499178,
    fullRecordGapCenterValue + 499370,
    fullRecordGapCenterValue + 499412,
    fullRecordGapCenterValue + 499430,
    fullRecordGapCenterValue + 499542,
    fullRecordGapCenterValue + 499602,
    fullRecordGapCenterValue + 499676,
    fullRecordGapCenterValue + 499706,
    fullRecordGapCenterValue + 499866,
    fullRecordGapCenterValue + 499886,
    fullRecordGapCenterValue + 499916,
    fullRecordGapCenterValue + 499976,
    fullRecordGapCenterValue + 500246,
    fullRecordGapCenterValue + 500252,
    fullRecordGapCenterValue + 500312,
    fullRecordGapCenterValue + 500330,
    fullRecordGapCenterValue + 500372,
    fullRecordGapCenterValue + 500406,
    fullRecordGapCenterValue + 500468,
    fullRecordGapCenterValue + 500510,
    fullRecordGapCenterValue + 500622,
    fullRecordGapCenterValue + 500690,
    fullRecordGapCenterValue + 500876,
    fullRecordGapCenterValue + 500882,
    fullRecordGapCenterValue + 500978,
    fullRecordGapCenterValue + 501086,
    fullRecordGapCenterValue + 501110,
    fullRecordGapCenterValue + 501362,
    fullRecordGapCenterValue + 501506,
    fullRecordGapCenterValue + 501548,
    fullRecordGapCenterValue + 501590,
    fullRecordGapCenterValue + 501692,
    fullRecordGapCenterValue + 501702,
    fullRecordGapCenterValue + 501716,
    fullRecordGapCenterValue + 501770,
    fullRecordGapCenterValue + 501848,
    fullRecordGapCenterValue + 501918,
    fullRecordGapCenterValue + 501938,
    fullRecordGapCenterValue + 501986,
    fullRecordGapCenterValue + 502070,
    fullRecordGapCenterValue + 502118,
    fullRecordGapCenterValue + 502310,
    fullRecordGapCenterValue + 502406,
    fullRecordGapCenterValue + 502526]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00132_fermat : ∀ n ∈ fullRecordGapRow00132_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08385_not_prime : ¬(recordGapCenter + 497066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497066]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08386_not_prime : ¬(recordGapCenter + 497298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497298]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08387_not_prime : ¬(recordGapCenter + 497348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497348]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08388_not_prime : ¬(recordGapCenter + 497390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497390]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08389_not_prime : ¬(recordGapCenter + 497418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497418]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08390_not_prime : ¬(recordGapCenter + 497498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497498]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08391_not_prime : ¬(recordGapCenter + 497732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497732]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08392_not_prime : ¬(recordGapCenter + 497738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497738]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08393_not_prime : ¬(recordGapCenter + 497786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497786]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08394_not_prime : ¬(recordGapCenter + 497870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497870]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08395_not_prime : ¬(recordGapCenter + 498036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498036]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08396_not_prime : ¬(recordGapCenter + 498282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498282]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08397_not_prime : ¬(recordGapCenter + 498398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498398]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08398_not_prime : ¬(recordGapCenter + 498558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498558]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08399_not_prime : ¬(recordGapCenter + 498572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498572]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08400_not_prime : ¬(recordGapCenter + 498702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498702]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08401_not_prime : ¬(recordGapCenter + 498716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498716]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08402_not_prime : ¬(recordGapCenter + 498776).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498776]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08403_not_prime : ¬(recordGapCenter + 498842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498842]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08404_not_prime : ¬(recordGapCenter + 498878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498878]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08405_not_prime : ¬(recordGapCenter + 499178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499178]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08406_not_prime : ¬(recordGapCenter + 499370).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499370]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08407_not_prime : ¬(recordGapCenter + 499412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499412]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08408_not_prime : ¬(recordGapCenter + 499430).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499430]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08409_not_prime : ¬(recordGapCenter + 499542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499542]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08410_not_prime : ¬(recordGapCenter + 499602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499602]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08411_not_prime : ¬(recordGapCenter + 499676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499676]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08412_not_prime : ¬(recordGapCenter + 499706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499706]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08413_not_prime : ¬(recordGapCenter + 499866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499866]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08414_not_prime : ¬(recordGapCenter + 499886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499886]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08415_not_prime : ¬(recordGapCenter + 499916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499916]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08416_not_prime : ¬(recordGapCenter + 499976).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499976]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08417_not_prime : ¬(recordGapCenter + 500246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500246]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08418_not_prime : ¬(recordGapCenter + 500252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500252]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08419_not_prime : ¬(recordGapCenter + 500312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500312]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08420_not_prime : ¬(recordGapCenter + 500330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500330]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08421_not_prime : ¬(recordGapCenter + 500372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500372]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08422_not_prime : ¬(recordGapCenter + 500406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500406]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08423_not_prime : ¬(recordGapCenter + 500468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500468]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08424_not_prime : ¬(recordGapCenter + 500510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500510]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08425_not_prime : ¬(recordGapCenter + 500622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500622]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08426_not_prime : ¬(recordGapCenter + 500690).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500690]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08427_not_prime : ¬(recordGapCenter + 500876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500876]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08428_not_prime : ¬(recordGapCenter + 500882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500882]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08429_not_prime : ¬(recordGapCenter + 500978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500978]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08430_not_prime : ¬(recordGapCenter + 501086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501086]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08431_not_prime : ¬(recordGapCenter + 501110).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501110]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08432_not_prime : ¬(recordGapCenter + 501362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501362]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08433_not_prime : ¬(recordGapCenter + 501506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501506]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08434_not_prime : ¬(recordGapCenter + 501548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501548]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08435_not_prime : ¬(recordGapCenter + 501590).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501590]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08436_not_prime : ¬(recordGapCenter + 501692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501692]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08437_not_prime : ¬(recordGapCenter + 501702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501702]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08438_not_prime : ¬(recordGapCenter + 501716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501716]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08439_not_prime : ¬(recordGapCenter + 501770).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501770]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08440_not_prime : ¬(recordGapCenter + 501848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501848]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08441_not_prime : ¬(recordGapCenter + 501918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501918]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08442_not_prime : ¬(recordGapCenter + 501938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501938]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08443_not_prime : ¬(recordGapCenter + 501986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501986]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08444_not_prime : ¬(recordGapCenter + 502070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502070]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08445_not_prime : ¬(recordGapCenter + 502118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502118]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08446_not_prime : ¬(recordGapCenter + 502310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502310]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08447_not_prime : ¬(recordGapCenter + 502406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502406]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

theorem fullRecordGapTerm08448_not_prime : ¬(recordGapCenter + 502526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502526]
  · apply fullRecordGapRow00132_fermat
    simp [fullRecordGapRow00132_values]

end PrimeFactorUnimodality
