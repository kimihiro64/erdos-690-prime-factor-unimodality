import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00152_values : List Nat :=
  [fullRecordGapCenterValue + 580430,
    fullRecordGapCenterValue + 580472,
    fullRecordGapCenterValue + 580578,
    fullRecordGapCenterValue + 580616,
    fullRecordGapCenterValue + 580722,
    fullRecordGapCenterValue + 580772,
    fullRecordGapCenterValue + 580886,
    fullRecordGapCenterValue + 580946,
    fullRecordGapCenterValue + 581018,
    fullRecordGapCenterValue + 581042,
    fullRecordGapCenterValue + 581246,
    fullRecordGapCenterValue + 581388,
    fullRecordGapCenterValue + 581432,
    fullRecordGapCenterValue + 581442,
    fullRecordGapCenterValue + 581466,
    fullRecordGapCenterValue + 581606,
    fullRecordGapCenterValue + 581732,
    fullRecordGapCenterValue + 581738,
    fullRecordGapCenterValue + 581772,
    fullRecordGapCenterValue + 581892,
    fullRecordGapCenterValue + 581942,
    fullRecordGapCenterValue + 581948,
    fullRecordGapCenterValue + 581982,
    fullRecordGapCenterValue + 582068,
    fullRecordGapCenterValue + 582086,
    fullRecordGapCenterValue + 582110,
    fullRecordGapCenterValue + 582120,
    fullRecordGapCenterValue + 582206,
    fullRecordGapCenterValue + 582356,
    fullRecordGapCenterValue + 582396,
    fullRecordGapCenterValue + 582398,
    fullRecordGapCenterValue + 582486,
    fullRecordGapCenterValue + 582548,
    fullRecordGapCenterValue + 582662,
    fullRecordGapCenterValue + 582702,
    fullRecordGapCenterValue + 582746,
    fullRecordGapCenterValue + 582836,
    fullRecordGapCenterValue + 582872,
    fullRecordGapCenterValue + 582878,
    fullRecordGapCenterValue + 582906,
    fullRecordGapCenterValue + 582962,
    fullRecordGapCenterValue + 583068,
    fullRecordGapCenterValue + 583112,
    fullRecordGapCenterValue + 583200,
    fullRecordGapCenterValue + 583278,
    fullRecordGapCenterValue + 583292,
    fullRecordGapCenterValue + 583322,
    fullRecordGapCenterValue + 583332,
    fullRecordGapCenterValue + 583382,
    fullRecordGapCenterValue + 583592,
    fullRecordGapCenterValue + 583706,
    fullRecordGapCenterValue + 583910,
    fullRecordGapCenterValue + 584138,
    fullRecordGapCenterValue + 584186,
    fullRecordGapCenterValue + 584202,
    fullRecordGapCenterValue + 584238,
    fullRecordGapCenterValue + 584252,
    fullRecordGapCenterValue + 584270,
    fullRecordGapCenterValue + 584286,
    fullRecordGapCenterValue + 584312,
    fullRecordGapCenterValue + 584322,
    fullRecordGapCenterValue + 584390,
    fullRecordGapCenterValue + 584462,
    fullRecordGapCenterValue + 584468]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00152_fermat : ∀ n ∈ fullRecordGapRow00152_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09665_not_prime : ¬(recordGapCenter + 580430).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580430]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09666_not_prime : ¬(recordGapCenter + 580472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580472]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09667_not_prime : ¬(recordGapCenter + 580578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580578]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09668_not_prime : ¬(recordGapCenter + 580616).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580616]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09669_not_prime : ¬(recordGapCenter + 580722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580722]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09670_not_prime : ¬(recordGapCenter + 580772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580772]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09671_not_prime : ¬(recordGapCenter + 580886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580886]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09672_not_prime : ¬(recordGapCenter + 580946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580946]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09673_not_prime : ¬(recordGapCenter + 581018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581018]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09674_not_prime : ¬(recordGapCenter + 581042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581042]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09675_not_prime : ¬(recordGapCenter + 581246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581246]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09676_not_prime : ¬(recordGapCenter + 581388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581388]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09677_not_prime : ¬(recordGapCenter + 581432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581432]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09678_not_prime : ¬(recordGapCenter + 581442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581442]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09679_not_prime : ¬(recordGapCenter + 581466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581466]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09680_not_prime : ¬(recordGapCenter + 581606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581606]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09681_not_prime : ¬(recordGapCenter + 581732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581732]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09682_not_prime : ¬(recordGapCenter + 581738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581738]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09683_not_prime : ¬(recordGapCenter + 581772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581772]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09684_not_prime : ¬(recordGapCenter + 581892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581892]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09685_not_prime : ¬(recordGapCenter + 581942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581942]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09686_not_prime : ¬(recordGapCenter + 581948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581948]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09687_not_prime : ¬(recordGapCenter + 581982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 581982]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09688_not_prime : ¬(recordGapCenter + 582068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582068]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09689_not_prime : ¬(recordGapCenter + 582086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582086]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09690_not_prime : ¬(recordGapCenter + 582110).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582110]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09691_not_prime : ¬(recordGapCenter + 582120).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582120]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09692_not_prime : ¬(recordGapCenter + 582206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582206]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09693_not_prime : ¬(recordGapCenter + 582356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582356]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09694_not_prime : ¬(recordGapCenter + 582396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582396]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09695_not_prime : ¬(recordGapCenter + 582398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582398]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09696_not_prime : ¬(recordGapCenter + 582486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582486]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09697_not_prime : ¬(recordGapCenter + 582548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582548]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09698_not_prime : ¬(recordGapCenter + 582662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582662]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09699_not_prime : ¬(recordGapCenter + 582702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582702]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09700_not_prime : ¬(recordGapCenter + 582746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582746]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09701_not_prime : ¬(recordGapCenter + 582836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582836]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09702_not_prime : ¬(recordGapCenter + 582872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582872]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09703_not_prime : ¬(recordGapCenter + 582878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582878]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09704_not_prime : ¬(recordGapCenter + 582906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582906]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09705_not_prime : ¬(recordGapCenter + 582962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 582962]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09706_not_prime : ¬(recordGapCenter + 583068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583068]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09707_not_prime : ¬(recordGapCenter + 583112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583112]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09708_not_prime : ¬(recordGapCenter + 583200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583200]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09709_not_prime : ¬(recordGapCenter + 583278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583278]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09710_not_prime : ¬(recordGapCenter + 583292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583292]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09711_not_prime : ¬(recordGapCenter + 583322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583322]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09712_not_prime : ¬(recordGapCenter + 583332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583332]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09713_not_prime : ¬(recordGapCenter + 583382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583382]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09714_not_prime : ¬(recordGapCenter + 583592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583592]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09715_not_prime : ¬(recordGapCenter + 583706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583706]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09716_not_prime : ¬(recordGapCenter + 583910).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 583910]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09717_not_prime : ¬(recordGapCenter + 584138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584138]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09718_not_prime : ¬(recordGapCenter + 584186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584186]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09719_not_prime : ¬(recordGapCenter + 584202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584202]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09720_not_prime : ¬(recordGapCenter + 584238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584238]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09721_not_prime : ¬(recordGapCenter + 584252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584252]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09722_not_prime : ¬(recordGapCenter + 584270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584270]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09723_not_prime : ¬(recordGapCenter + 584286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584286]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09724_not_prime : ¬(recordGapCenter + 584312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584312]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09725_not_prime : ¬(recordGapCenter + 584322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584322]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09726_not_prime : ¬(recordGapCenter + 584390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584390]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09727_not_prime : ¬(recordGapCenter + 584462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584462]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

theorem fullRecordGapTerm09728_not_prime : ¬(recordGapCenter + 584468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 584468]
  · apply fullRecordGapRow00152_fermat
    simp [fullRecordGapRow00152_values]

end PrimeFactorUnimodality
