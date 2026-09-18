import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00116_values : List Nat :=
  [fullRecordGapCenterValue + 423032,
    fullRecordGapCenterValue + 423068,
    fullRecordGapCenterValue + 423146,
    fullRecordGapCenterValue + 423278,
    fullRecordGapCenterValue + 423360,
    fullRecordGapCenterValue + 423426,
    fullRecordGapCenterValue + 423498,
    fullRecordGapCenterValue + 423578,
    fullRecordGapCenterValue + 423596,
    fullRecordGapCenterValue + 423602,
    fullRecordGapCenterValue + 423608,
    fullRecordGapCenterValue + 423642,
    fullRecordGapCenterValue + 423726,
    fullRecordGapCenterValue + 423866,
    fullRecordGapCenterValue + 423908,
    fullRecordGapCenterValue + 423932,
    fullRecordGapCenterValue + 423942,
    fullRecordGapCenterValue + 424058,
    fullRecordGapCenterValue + 424406,
    fullRecordGapCenterValue + 424412,
    fullRecordGapCenterValue + 424478,
    fullRecordGapCenterValue + 424562,
    fullRecordGapCenterValue + 424698,
    fullRecordGapCenterValue + 424868,
    fullRecordGapCenterValue + 424938,
    fullRecordGapCenterValue + 425118,
    fullRecordGapCenterValue + 425192,
    fullRecordGapCenterValue + 425342,
    fullRecordGapCenterValue + 425346,
    fullRecordGapCenterValue + 425402,
    fullRecordGapCenterValue + 425406,
    fullRecordGapCenterValue + 425468,
    fullRecordGapCenterValue + 425492,
    fullRecordGapCenterValue + 425576,
    fullRecordGapCenterValue + 425582,
    fullRecordGapCenterValue + 425622,
    fullRecordGapCenterValue + 425708,
    fullRecordGapCenterValue + 425846,
    fullRecordGapCenterValue + 425912,
    fullRecordGapCenterValue + 425948,
    fullRecordGapCenterValue + 426038,
    fullRecordGapCenterValue + 426086,
    fullRecordGapCenterValue + 426182,
    fullRecordGapCenterValue + 426248,
    fullRecordGapCenterValue + 426386,
    fullRecordGapCenterValue + 426486,
    fullRecordGapCenterValue + 426506,
    fullRecordGapCenterValue + 426638,
    fullRecordGapCenterValue + 426882,
    fullRecordGapCenterValue + 426918,
    fullRecordGapCenterValue + 426956,
    fullRecordGapCenterValue + 426962,
    fullRecordGapCenterValue + 426966,
    fullRecordGapCenterValue + 427106,
    fullRecordGapCenterValue + 427208,
    fullRecordGapCenterValue + 427256,
    fullRecordGapCenterValue + 427292,
    fullRecordGapCenterValue + 427352,
    fullRecordGapCenterValue + 427442,
    fullRecordGapCenterValue + 427502,
    fullRecordGapCenterValue + 427628,
    fullRecordGapCenterValue + 427680,
    fullRecordGapCenterValue + 427718,
    fullRecordGapCenterValue + 427758]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00116_fermat : ∀ n ∈ fullRecordGapRow00116_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07361_not_prime : ¬(recordGapCenter + 423032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423032]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07362_not_prime : ¬(recordGapCenter + 423068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423068]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07363_not_prime : ¬(recordGapCenter + 423146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423146]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07364_not_prime : ¬(recordGapCenter + 423278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423278]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07365_not_prime : ¬(recordGapCenter + 423360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423360]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07366_not_prime : ¬(recordGapCenter + 423426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423426]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07367_not_prime : ¬(recordGapCenter + 423498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423498]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07368_not_prime : ¬(recordGapCenter + 423578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423578]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07369_not_prime : ¬(recordGapCenter + 423596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423596]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07370_not_prime : ¬(recordGapCenter + 423602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423602]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07371_not_prime : ¬(recordGapCenter + 423608).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423608]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07372_not_prime : ¬(recordGapCenter + 423642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423642]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07373_not_prime : ¬(recordGapCenter + 423726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423726]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07374_not_prime : ¬(recordGapCenter + 423866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423866]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07375_not_prime : ¬(recordGapCenter + 423908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423908]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07376_not_prime : ¬(recordGapCenter + 423932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423932]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07377_not_prime : ¬(recordGapCenter + 423942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 423942]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07378_not_prime : ¬(recordGapCenter + 424058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 424058]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07379_not_prime : ¬(recordGapCenter + 424406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 424406]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07380_not_prime : ¬(recordGapCenter + 424412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 424412]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07381_not_prime : ¬(recordGapCenter + 424478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 424478]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07382_not_prime : ¬(recordGapCenter + 424562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 424562]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07383_not_prime : ¬(recordGapCenter + 424698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 424698]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07384_not_prime : ¬(recordGapCenter + 424868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 424868]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07385_not_prime : ¬(recordGapCenter + 424938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 424938]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07386_not_prime : ¬(recordGapCenter + 425118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425118]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07387_not_prime : ¬(recordGapCenter + 425192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425192]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07388_not_prime : ¬(recordGapCenter + 425342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425342]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07389_not_prime : ¬(recordGapCenter + 425346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425346]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07390_not_prime : ¬(recordGapCenter + 425402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425402]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07391_not_prime : ¬(recordGapCenter + 425406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425406]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07392_not_prime : ¬(recordGapCenter + 425468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425468]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07393_not_prime : ¬(recordGapCenter + 425492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425492]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07394_not_prime : ¬(recordGapCenter + 425576).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425576]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07395_not_prime : ¬(recordGapCenter + 425582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425582]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07396_not_prime : ¬(recordGapCenter + 425622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425622]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07397_not_prime : ¬(recordGapCenter + 425708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425708]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07398_not_prime : ¬(recordGapCenter + 425846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425846]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07399_not_prime : ¬(recordGapCenter + 425912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425912]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07400_not_prime : ¬(recordGapCenter + 425948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 425948]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07401_not_prime : ¬(recordGapCenter + 426038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 426038]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07402_not_prime : ¬(recordGapCenter + 426086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 426086]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07403_not_prime : ¬(recordGapCenter + 426182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 426182]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07404_not_prime : ¬(recordGapCenter + 426248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 426248]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07405_not_prime : ¬(recordGapCenter + 426386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 426386]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07406_not_prime : ¬(recordGapCenter + 426486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 426486]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07407_not_prime : ¬(recordGapCenter + 426506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 426506]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07408_not_prime : ¬(recordGapCenter + 426638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 426638]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07409_not_prime : ¬(recordGapCenter + 426882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 426882]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07410_not_prime : ¬(recordGapCenter + 426918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 426918]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07411_not_prime : ¬(recordGapCenter + 426956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 426956]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07412_not_prime : ¬(recordGapCenter + 426962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 426962]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07413_not_prime : ¬(recordGapCenter + 426966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 426966]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07414_not_prime : ¬(recordGapCenter + 427106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 427106]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07415_not_prime : ¬(recordGapCenter + 427208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 427208]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07416_not_prime : ¬(recordGapCenter + 427256).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 427256]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07417_not_prime : ¬(recordGapCenter + 427292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 427292]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07418_not_prime : ¬(recordGapCenter + 427352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 427352]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07419_not_prime : ¬(recordGapCenter + 427442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 427442]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07420_not_prime : ¬(recordGapCenter + 427502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 427502]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07421_not_prime : ¬(recordGapCenter + 427628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 427628]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07422_not_prime : ¬(recordGapCenter + 427680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 427680]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07423_not_prime : ¬(recordGapCenter + 427718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 427718]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

theorem fullRecordGapTerm07424_not_prime : ¬(recordGapCenter + 427758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 427758]
  · apply fullRecordGapRow00116_fermat
    simp [fullRecordGapRow00116_values]

end PrimeFactorUnimodality
