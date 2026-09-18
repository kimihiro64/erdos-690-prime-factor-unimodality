import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00150_values : List Nat :=
  [fullRecordGapCenterValue + 572126,
    fullRecordGapCenterValue + 572210,
    fullRecordGapCenterValue + 572342,
    fullRecordGapCenterValue + 572412,
    fullRecordGapCenterValue + 572478,
    fullRecordGapCenterValue + 572498,
    fullRecordGapCenterValue + 572510,
    fullRecordGapCenterValue + 572532,
    fullRecordGapCenterValue + 572552,
    fullRecordGapCenterValue + 572556,
    fullRecordGapCenterValue + 572646,
    fullRecordGapCenterValue + 572658,
    fullRecordGapCenterValue + 572708,
    fullRecordGapCenterValue + 572786,
    fullRecordGapCenterValue + 572826,
    fullRecordGapCenterValue + 572870,
    fullRecordGapCenterValue + 572996,
    fullRecordGapCenterValue + 573176,
    fullRecordGapCenterValue + 573290,
    fullRecordGapCenterValue + 573332,
    fullRecordGapCenterValue + 573422,
    fullRecordGapCenterValue + 573440,
    fullRecordGapCenterValue + 573486,
    fullRecordGapCenterValue + 573548,
    fullRecordGapCenterValue + 573618,
    fullRecordGapCenterValue + 573626,
    fullRecordGapCenterValue + 573662,
    fullRecordGapCenterValue + 573702,
    fullRecordGapCenterValue + 573708,
    fullRecordGapCenterValue + 573746,
    fullRecordGapCenterValue + 573828,
    fullRecordGapCenterValue + 573890,
    fullRecordGapCenterValue + 573962,
    fullRecordGapCenterValue + 574268,
    fullRecordGapCenterValue + 574278,
    fullRecordGapCenterValue + 574358,
    fullRecordGapCenterValue + 574382,
    fullRecordGapCenterValue + 574386,
    fullRecordGapCenterValue + 574428,
    fullRecordGapCenterValue + 574466,
    fullRecordGapCenterValue + 574502,
    fullRecordGapCenterValue + 574562,
    fullRecordGapCenterValue + 574568,
    fullRecordGapCenterValue + 574572,
    fullRecordGapCenterValue + 574676,
    fullRecordGapCenterValue + 574796,
    fullRecordGapCenterValue + 574806,
    fullRecordGapCenterValue + 574836,
    fullRecordGapCenterValue + 574898,
    fullRecordGapCenterValue + 575048,
    fullRecordGapCenterValue + 575096,
    fullRecordGapCenterValue + 575258,
    fullRecordGapCenterValue + 575268,
    fullRecordGapCenterValue + 575286,
    fullRecordGapCenterValue + 575342,
    fullRecordGapCenterValue + 575466,
    fullRecordGapCenterValue + 575502,
    fullRecordGapCenterValue + 575556,
    fullRecordGapCenterValue + 575576,
    fullRecordGapCenterValue + 575628,
    fullRecordGapCenterValue + 575636,
    fullRecordGapCenterValue + 575642,
    fullRecordGapCenterValue + 575682,
    fullRecordGapCenterValue + 575702]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00150_fermat : ∀ n ∈ fullRecordGapRow00150_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09537_not_prime : ¬(recordGapCenter + 572126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572126]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09538_not_prime : ¬(recordGapCenter + 572210).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572210]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09539_not_prime : ¬(recordGapCenter + 572342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572342]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09540_not_prime : ¬(recordGapCenter + 572412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572412]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09541_not_prime : ¬(recordGapCenter + 572478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572478]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09542_not_prime : ¬(recordGapCenter + 572498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572498]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09543_not_prime : ¬(recordGapCenter + 572510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572510]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09544_not_prime : ¬(recordGapCenter + 572532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572532]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09545_not_prime : ¬(recordGapCenter + 572552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572552]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09546_not_prime : ¬(recordGapCenter + 572556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572556]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09547_not_prime : ¬(recordGapCenter + 572646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572646]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09548_not_prime : ¬(recordGapCenter + 572658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572658]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09549_not_prime : ¬(recordGapCenter + 572708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572708]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09550_not_prime : ¬(recordGapCenter + 572786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572786]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09551_not_prime : ¬(recordGapCenter + 572826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572826]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09552_not_prime : ¬(recordGapCenter + 572870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572870]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09553_not_prime : ¬(recordGapCenter + 572996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 572996]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09554_not_prime : ¬(recordGapCenter + 573176).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573176]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09555_not_prime : ¬(recordGapCenter + 573290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573290]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09556_not_prime : ¬(recordGapCenter + 573332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573332]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09557_not_prime : ¬(recordGapCenter + 573422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573422]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09558_not_prime : ¬(recordGapCenter + 573440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573440]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09559_not_prime : ¬(recordGapCenter + 573486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573486]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09560_not_prime : ¬(recordGapCenter + 573548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573548]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09561_not_prime : ¬(recordGapCenter + 573618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573618]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09562_not_prime : ¬(recordGapCenter + 573626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573626]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09563_not_prime : ¬(recordGapCenter + 573662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573662]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09564_not_prime : ¬(recordGapCenter + 573702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573702]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09565_not_prime : ¬(recordGapCenter + 573708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573708]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09566_not_prime : ¬(recordGapCenter + 573746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573746]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09567_not_prime : ¬(recordGapCenter + 573828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573828]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09568_not_prime : ¬(recordGapCenter + 573890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573890]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09569_not_prime : ¬(recordGapCenter + 573962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 573962]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09570_not_prime : ¬(recordGapCenter + 574268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574268]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09571_not_prime : ¬(recordGapCenter + 574278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574278]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09572_not_prime : ¬(recordGapCenter + 574358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574358]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09573_not_prime : ¬(recordGapCenter + 574382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574382]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09574_not_prime : ¬(recordGapCenter + 574386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574386]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09575_not_prime : ¬(recordGapCenter + 574428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574428]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09576_not_prime : ¬(recordGapCenter + 574466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574466]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09577_not_prime : ¬(recordGapCenter + 574502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574502]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09578_not_prime : ¬(recordGapCenter + 574562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574562]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09579_not_prime : ¬(recordGapCenter + 574568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574568]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09580_not_prime : ¬(recordGapCenter + 574572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574572]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09581_not_prime : ¬(recordGapCenter + 574676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574676]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09582_not_prime : ¬(recordGapCenter + 574796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574796]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09583_not_prime : ¬(recordGapCenter + 574806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574806]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09584_not_prime : ¬(recordGapCenter + 574836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574836]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09585_not_prime : ¬(recordGapCenter + 574898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 574898]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09586_not_prime : ¬(recordGapCenter + 575048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575048]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09587_not_prime : ¬(recordGapCenter + 575096).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575096]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09588_not_prime : ¬(recordGapCenter + 575258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575258]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09589_not_prime : ¬(recordGapCenter + 575268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575268]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09590_not_prime : ¬(recordGapCenter + 575286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575286]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09591_not_prime : ¬(recordGapCenter + 575342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575342]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09592_not_prime : ¬(recordGapCenter + 575466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575466]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09593_not_prime : ¬(recordGapCenter + 575502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575502]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09594_not_prime : ¬(recordGapCenter + 575556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575556]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09595_not_prime : ¬(recordGapCenter + 575576).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575576]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09596_not_prime : ¬(recordGapCenter + 575628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575628]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09597_not_prime : ¬(recordGapCenter + 575636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575636]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09598_not_prime : ¬(recordGapCenter + 575642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575642]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09599_not_prime : ¬(recordGapCenter + 575682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575682]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

theorem fullRecordGapTerm09600_not_prime : ¬(recordGapCenter + 575702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575702]
  · apply fullRecordGapRow00150_fermat
    simp [fullRecordGapRow00150_values]

end PrimeFactorUnimodality
