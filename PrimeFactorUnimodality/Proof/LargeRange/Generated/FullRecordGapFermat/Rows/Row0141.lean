import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00141_values : List Nat :=
  [fullRecordGapCenterValue + 536412,
    fullRecordGapCenterValue + 536478,
    fullRecordGapCenterValue + 536582,
    fullRecordGapCenterValue + 536586,
    fullRecordGapCenterValue + 536748,
    fullRecordGapCenterValue + 536828,
    fullRecordGapCenterValue + 536852,
    fullRecordGapCenterValue + 536918,
    fullRecordGapCenterValue + 536930,
    fullRecordGapCenterValue + 536946,
    fullRecordGapCenterValue + 537002,
    fullRecordGapCenterValue + 537062,
    fullRecordGapCenterValue + 537252,
    fullRecordGapCenterValue + 537308,
    fullRecordGapCenterValue + 537332,
    fullRecordGapCenterValue + 537378,
    fullRecordGapCenterValue + 537386,
    fullRecordGapCenterValue + 537402,
    fullRecordGapCenterValue + 537468,
    fullRecordGapCenterValue + 537476,
    fullRecordGapCenterValue + 537512,
    fullRecordGapCenterValue + 537518,
    fullRecordGapCenterValue + 537546,
    fullRecordGapCenterValue + 537582,
    fullRecordGapCenterValue + 537590,
    fullRecordGapCenterValue + 537600,
    fullRecordGapCenterValue + 537626,
    fullRecordGapCenterValue + 537638,
    fullRecordGapCenterValue + 537666,
    fullRecordGapCenterValue + 537668,
    fullRecordGapCenterValue + 537722,
    fullRecordGapCenterValue + 537752,
    fullRecordGapCenterValue + 537762,
    fullRecordGapCenterValue + 537818,
    fullRecordGapCenterValue + 537848,
    fullRecordGapCenterValue + 537986,
    fullRecordGapCenterValue + 538046,
    fullRecordGapCenterValue + 538058,
    fullRecordGapCenterValue + 538086,
    fullRecordGapCenterValue + 538130,
    fullRecordGapCenterValue + 538178,
    fullRecordGapCenterValue + 538190,
    fullRecordGapCenterValue + 538310,
    fullRecordGapCenterValue + 538436,
    fullRecordGapCenterValue + 538562,
    fullRecordGapCenterValue + 538610,
    fullRecordGapCenterValue + 538676,
    fullRecordGapCenterValue + 538682,
    fullRecordGapCenterValue + 538910,
    fullRecordGapCenterValue + 538926,
    fullRecordGapCenterValue + 538970,
    fullRecordGapCenterValue + 539108,
    fullRecordGapCenterValue + 539228,
    fullRecordGapCenterValue + 539246,
    fullRecordGapCenterValue + 539270,
    fullRecordGapCenterValue + 539288,
    fullRecordGapCenterValue + 539390,
    fullRecordGapCenterValue + 539402,
    fullRecordGapCenterValue + 539438,
    fullRecordGapCenterValue + 539498,
    fullRecordGapCenterValue + 539556,
    fullRecordGapCenterValue + 539576,
    fullRecordGapCenterValue + 539582,
    fullRecordGapCenterValue + 539652]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00141_fermat : ∀ n ∈ fullRecordGapRow00141_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08961_not_prime : ¬(recordGapCenter + 536412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536412]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08962_not_prime : ¬(recordGapCenter + 536478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536478]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08963_not_prime : ¬(recordGapCenter + 536582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536582]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08964_not_prime : ¬(recordGapCenter + 536586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536586]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08965_not_prime : ¬(recordGapCenter + 536748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536748]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08966_not_prime : ¬(recordGapCenter + 536828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536828]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08967_not_prime : ¬(recordGapCenter + 536852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536852]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08968_not_prime : ¬(recordGapCenter + 536918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536918]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08969_not_prime : ¬(recordGapCenter + 536930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536930]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08970_not_prime : ¬(recordGapCenter + 536946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536946]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08971_not_prime : ¬(recordGapCenter + 537002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537002]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08972_not_prime : ¬(recordGapCenter + 537062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537062]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08973_not_prime : ¬(recordGapCenter + 537252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537252]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08974_not_prime : ¬(recordGapCenter + 537308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537308]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08975_not_prime : ¬(recordGapCenter + 537332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537332]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08976_not_prime : ¬(recordGapCenter + 537378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537378]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08977_not_prime : ¬(recordGapCenter + 537386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537386]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08978_not_prime : ¬(recordGapCenter + 537402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537402]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08979_not_prime : ¬(recordGapCenter + 537468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537468]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08980_not_prime : ¬(recordGapCenter + 537476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537476]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08981_not_prime : ¬(recordGapCenter + 537512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537512]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08982_not_prime : ¬(recordGapCenter + 537518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537518]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08983_not_prime : ¬(recordGapCenter + 537546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537546]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08984_not_prime : ¬(recordGapCenter + 537582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537582]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08985_not_prime : ¬(recordGapCenter + 537590).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537590]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08986_not_prime : ¬(recordGapCenter + 537600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537600]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08987_not_prime : ¬(recordGapCenter + 537626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537626]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08988_not_prime : ¬(recordGapCenter + 537638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537638]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08989_not_prime : ¬(recordGapCenter + 537666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537666]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08990_not_prime : ¬(recordGapCenter + 537668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537668]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08991_not_prime : ¬(recordGapCenter + 537722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537722]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08992_not_prime : ¬(recordGapCenter + 537752).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537752]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08993_not_prime : ¬(recordGapCenter + 537762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537762]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08994_not_prime : ¬(recordGapCenter + 537818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537818]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08995_not_prime : ¬(recordGapCenter + 537848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537848]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08996_not_prime : ¬(recordGapCenter + 537986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 537986]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08997_not_prime : ¬(recordGapCenter + 538046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538046]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08998_not_prime : ¬(recordGapCenter + 538058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538058]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm08999_not_prime : ¬(recordGapCenter + 538086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538086]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09000_not_prime : ¬(recordGapCenter + 538130).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538130]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09001_not_prime : ¬(recordGapCenter + 538178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538178]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09002_not_prime : ¬(recordGapCenter + 538190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538190]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09003_not_prime : ¬(recordGapCenter + 538310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538310]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09004_not_prime : ¬(recordGapCenter + 538436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538436]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09005_not_prime : ¬(recordGapCenter + 538562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538562]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09006_not_prime : ¬(recordGapCenter + 538610).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538610]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09007_not_prime : ¬(recordGapCenter + 538676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538676]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09008_not_prime : ¬(recordGapCenter + 538682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538682]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09009_not_prime : ¬(recordGapCenter + 538910).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538910]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09010_not_prime : ¬(recordGapCenter + 538926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538926]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09011_not_prime : ¬(recordGapCenter + 538970).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 538970]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09012_not_prime : ¬(recordGapCenter + 539108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539108]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09013_not_prime : ¬(recordGapCenter + 539228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539228]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09014_not_prime : ¬(recordGapCenter + 539246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539246]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09015_not_prime : ¬(recordGapCenter + 539270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539270]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09016_not_prime : ¬(recordGapCenter + 539288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539288]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09017_not_prime : ¬(recordGapCenter + 539390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539390]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09018_not_prime : ¬(recordGapCenter + 539402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539402]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09019_not_prime : ¬(recordGapCenter + 539438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539438]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09020_not_prime : ¬(recordGapCenter + 539498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539498]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09021_not_prime : ¬(recordGapCenter + 539556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539556]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09022_not_prime : ¬(recordGapCenter + 539576).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539576]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09023_not_prime : ¬(recordGapCenter + 539582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539582]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

theorem fullRecordGapTerm09024_not_prime : ¬(recordGapCenter + 539652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 539652]
  · apply fullRecordGapRow00141_fermat
    simp [fullRecordGapRow00141_values]

end PrimeFactorUnimodality
