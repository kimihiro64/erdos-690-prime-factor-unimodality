import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00105_values : List Nat :=
  [fullRecordGapCenterValue + 368582,
    fullRecordGapCenterValue + 368618,
    fullRecordGapCenterValue + 368642,
    fullRecordGapCenterValue + 368666,
    fullRecordGapCenterValue + 368898,
    fullRecordGapCenterValue + 368972,
    fullRecordGapCenterValue + 369128,
    fullRecordGapCenterValue + 369218,
    fullRecordGapCenterValue + 369302,
    fullRecordGapCenterValue + 369428,
    fullRecordGapCenterValue + 369476,
    fullRecordGapCenterValue + 369506,
    fullRecordGapCenterValue + 369752,
    fullRecordGapCenterValue + 369758,
    fullRecordGapCenterValue + 369906,
    fullRecordGapCenterValue + 369986,
    fullRecordGapCenterValue + 370002,
    fullRecordGapCenterValue + 370086,
    fullRecordGapCenterValue + 370088,
    fullRecordGapCenterValue + 370122,
    fullRecordGapCenterValue + 370232,
    fullRecordGapCenterValue + 370262,
    fullRecordGapCenterValue + 370338,
    fullRecordGapCenterValue + 370472,
    fullRecordGapCenterValue + 370506,
    fullRecordGapCenterValue + 370598,
    fullRecordGapCenterValue + 370646,
    fullRecordGapCenterValue + 370676,
    fullRecordGapCenterValue + 370686,
    fullRecordGapCenterValue + 370742,
    fullRecordGapCenterValue + 370802,
    fullRecordGapCenterValue + 370868,
    fullRecordGapCenterValue + 370892,
    fullRecordGapCenterValue + 371012,
    fullRecordGapCenterValue + 371058,
    fullRecordGapCenterValue + 371066,
    fullRecordGapCenterValue + 371250,
    fullRecordGapCenterValue + 371288,
    fullRecordGapCenterValue + 371366,
    fullRecordGapCenterValue + 371498,
    fullRecordGapCenterValue + 371528,
    fullRecordGapCenterValue + 371666,
    fullRecordGapCenterValue + 371738,
    fullRecordGapCenterValue + 371886,
    fullRecordGapCenterValue + 371946,
    fullRecordGapCenterValue + 372282,
    fullRecordGapCenterValue + 372332,
    fullRecordGapCenterValue + 372342,
    fullRecordGapCenterValue + 372426,
    fullRecordGapCenterValue + 372486,
    fullRecordGapCenterValue + 372536,
    fullRecordGapCenterValue + 372542,
    fullRecordGapCenterValue + 372680,
    fullRecordGapCenterValue + 372782,
    fullRecordGapCenterValue + 372822,
    fullRecordGapCenterValue + 372858,
    fullRecordGapCenterValue + 372902,
    fullRecordGapCenterValue + 372956,
    fullRecordGapCenterValue + 373026,
    fullRecordGapCenterValue + 373052,
    fullRecordGapCenterValue + 373112,
    fullRecordGapCenterValue + 373146,
    fullRecordGapCenterValue + 373206,
    fullRecordGapCenterValue + 373238]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00105_fermat : ∀ n ∈ fullRecordGapRow00105_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06657_not_prime : ¬(recordGapCenter + 368582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368582]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06658_not_prime : ¬(recordGapCenter + 368618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368618]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06659_not_prime : ¬(recordGapCenter + 368642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368642]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06660_not_prime : ¬(recordGapCenter + 368666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368666]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06661_not_prime : ¬(recordGapCenter + 368898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368898]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06662_not_prime : ¬(recordGapCenter + 368972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 368972]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06663_not_prime : ¬(recordGapCenter + 369128).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369128]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06664_not_prime : ¬(recordGapCenter + 369218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369218]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06665_not_prime : ¬(recordGapCenter + 369302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369302]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06666_not_prime : ¬(recordGapCenter + 369428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369428]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06667_not_prime : ¬(recordGapCenter + 369476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369476]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06668_not_prime : ¬(recordGapCenter + 369506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369506]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06669_not_prime : ¬(recordGapCenter + 369752).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369752]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06670_not_prime : ¬(recordGapCenter + 369758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369758]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06671_not_prime : ¬(recordGapCenter + 369906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369906]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06672_not_prime : ¬(recordGapCenter + 369986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 369986]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06673_not_prime : ¬(recordGapCenter + 370002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370002]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06674_not_prime : ¬(recordGapCenter + 370086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370086]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06675_not_prime : ¬(recordGapCenter + 370088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370088]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06676_not_prime : ¬(recordGapCenter + 370122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370122]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06677_not_prime : ¬(recordGapCenter + 370232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370232]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06678_not_prime : ¬(recordGapCenter + 370262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370262]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06679_not_prime : ¬(recordGapCenter + 370338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370338]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06680_not_prime : ¬(recordGapCenter + 370472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370472]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06681_not_prime : ¬(recordGapCenter + 370506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370506]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06682_not_prime : ¬(recordGapCenter + 370598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370598]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06683_not_prime : ¬(recordGapCenter + 370646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370646]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06684_not_prime : ¬(recordGapCenter + 370676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370676]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06685_not_prime : ¬(recordGapCenter + 370686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370686]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06686_not_prime : ¬(recordGapCenter + 370742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370742]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06687_not_prime : ¬(recordGapCenter + 370802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370802]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06688_not_prime : ¬(recordGapCenter + 370868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370868]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06689_not_prime : ¬(recordGapCenter + 370892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 370892]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06690_not_prime : ¬(recordGapCenter + 371012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371012]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06691_not_prime : ¬(recordGapCenter + 371058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371058]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06692_not_prime : ¬(recordGapCenter + 371066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371066]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06693_not_prime : ¬(recordGapCenter + 371250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371250]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06694_not_prime : ¬(recordGapCenter + 371288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371288]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06695_not_prime : ¬(recordGapCenter + 371366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371366]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06696_not_prime : ¬(recordGapCenter + 371498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371498]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06697_not_prime : ¬(recordGapCenter + 371528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371528]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06698_not_prime : ¬(recordGapCenter + 371666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371666]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06699_not_prime : ¬(recordGapCenter + 371738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371738]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06700_not_prime : ¬(recordGapCenter + 371886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371886]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06701_not_prime : ¬(recordGapCenter + 371946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 371946]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06702_not_prime : ¬(recordGapCenter + 372282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372282]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06703_not_prime : ¬(recordGapCenter + 372332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372332]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06704_not_prime : ¬(recordGapCenter + 372342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372342]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06705_not_prime : ¬(recordGapCenter + 372426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372426]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06706_not_prime : ¬(recordGapCenter + 372486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372486]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06707_not_prime : ¬(recordGapCenter + 372536).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372536]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06708_not_prime : ¬(recordGapCenter + 372542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372542]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06709_not_prime : ¬(recordGapCenter + 372680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372680]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06710_not_prime : ¬(recordGapCenter + 372782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372782]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06711_not_prime : ¬(recordGapCenter + 372822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372822]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06712_not_prime : ¬(recordGapCenter + 372858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372858]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06713_not_prime : ¬(recordGapCenter + 372902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372902]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06714_not_prime : ¬(recordGapCenter + 372956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 372956]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06715_not_prime : ¬(recordGapCenter + 373026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373026]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06716_not_prime : ¬(recordGapCenter + 373052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373052]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06717_not_prime : ¬(recordGapCenter + 373112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373112]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06718_not_prime : ¬(recordGapCenter + 373146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373146]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06719_not_prime : ¬(recordGapCenter + 373206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373206]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

theorem fullRecordGapTerm06720_not_prime : ¬(recordGapCenter + 373238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 373238]
  · apply fullRecordGapRow00105_fermat
    simp [fullRecordGapRow00105_values]

end PrimeFactorUnimodality
