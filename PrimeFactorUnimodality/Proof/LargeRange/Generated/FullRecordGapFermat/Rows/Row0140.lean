import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00140_values : List Nat :=
  [fullRecordGapCenterValue + 532446,
    fullRecordGapCenterValue + 532802,
    fullRecordGapCenterValue + 532806,
    fullRecordGapCenterValue + 532808,
    fullRecordGapCenterValue + 532842,
    fullRecordGapCenterValue + 532866,
    fullRecordGapCenterValue + 533108,
    fullRecordGapCenterValue + 533118,
    fullRecordGapCenterValue + 533270,
    fullRecordGapCenterValue + 533348,
    fullRecordGapCenterValue + 533366,
    fullRecordGapCenterValue + 533396,
    fullRecordGapCenterValue + 533436,
    fullRecordGapCenterValue + 533438,
    fullRecordGapCenterValue + 533576,
    fullRecordGapCenterValue + 533612,
    fullRecordGapCenterValue + 533642,
    fullRecordGapCenterValue + 533678,
    fullRecordGapCenterValue + 533726,
    fullRecordGapCenterValue + 533810,
    fullRecordGapCenterValue + 533906,
    fullRecordGapCenterValue + 533942,
    fullRecordGapCenterValue + 533972,
    fullRecordGapCenterValue + 533982,
    fullRecordGapCenterValue + 533996,
    fullRecordGapCenterValue + 534098,
    fullRecordGapCenterValue + 534102,
    fullRecordGapCenterValue + 534426,
    fullRecordGapCenterValue + 534516,
    fullRecordGapCenterValue + 534518,
    fullRecordGapCenterValue + 534542,
    fullRecordGapCenterValue + 534600,
    fullRecordGapCenterValue + 534642,
    fullRecordGapCenterValue + 534782,
    fullRecordGapCenterValue + 534822,
    fullRecordGapCenterValue + 534902,
    fullRecordGapCenterValue + 534938,
    fullRecordGapCenterValue + 534962,
    fullRecordGapCenterValue + 535070,
    fullRecordGapCenterValue + 535076,
    fullRecordGapCenterValue + 535202,
    fullRecordGapCenterValue + 535286,
    fullRecordGapCenterValue + 535362,
    fullRecordGapCenterValue + 535386,
    fullRecordGapCenterValue + 535442,
    fullRecordGapCenterValue + 535452,
    fullRecordGapCenterValue + 535566,
    fullRecordGapCenterValue + 535592,
    fullRecordGapCenterValue + 535802,
    fullRecordGapCenterValue + 535812,
    fullRecordGapCenterValue + 535818,
    fullRecordGapCenterValue + 535826,
    fullRecordGapCenterValue + 535910,
    fullRecordGapCenterValue + 536006,
    fullRecordGapCenterValue + 536126,
    fullRecordGapCenterValue + 536138,
    fullRecordGapCenterValue + 536168,
    fullRecordGapCenterValue + 536196,
    fullRecordGapCenterValue + 536226,
    fullRecordGapCenterValue + 536286,
    fullRecordGapCenterValue + 536306,
    fullRecordGapCenterValue + 536342,
    fullRecordGapCenterValue + 536348,
    fullRecordGapCenterValue + 536372]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00140_fermat : ∀ n ∈ fullRecordGapRow00140_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08897_not_prime : ¬(recordGapCenter + 532446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532446]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08898_not_prime : ¬(recordGapCenter + 532802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532802]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08899_not_prime : ¬(recordGapCenter + 532806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532806]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08900_not_prime : ¬(recordGapCenter + 532808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532808]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08901_not_prime : ¬(recordGapCenter + 532842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532842]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08902_not_prime : ¬(recordGapCenter + 532866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 532866]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08903_not_prime : ¬(recordGapCenter + 533108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533108]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08904_not_prime : ¬(recordGapCenter + 533118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533118]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08905_not_prime : ¬(recordGapCenter + 533270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533270]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08906_not_prime : ¬(recordGapCenter + 533348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533348]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08907_not_prime : ¬(recordGapCenter + 533366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533366]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08908_not_prime : ¬(recordGapCenter + 533396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533396]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08909_not_prime : ¬(recordGapCenter + 533436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533436]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08910_not_prime : ¬(recordGapCenter + 533438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533438]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08911_not_prime : ¬(recordGapCenter + 533576).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533576]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08912_not_prime : ¬(recordGapCenter + 533612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533612]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08913_not_prime : ¬(recordGapCenter + 533642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533642]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08914_not_prime : ¬(recordGapCenter + 533678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533678]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08915_not_prime : ¬(recordGapCenter + 533726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533726]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08916_not_prime : ¬(recordGapCenter + 533810).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533810]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08917_not_prime : ¬(recordGapCenter + 533906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533906]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08918_not_prime : ¬(recordGapCenter + 533942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533942]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08919_not_prime : ¬(recordGapCenter + 533972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533972]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08920_not_prime : ¬(recordGapCenter + 533982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533982]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08921_not_prime : ¬(recordGapCenter + 533996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 533996]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08922_not_prime : ¬(recordGapCenter + 534098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 534098]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08923_not_prime : ¬(recordGapCenter + 534102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 534102]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08924_not_prime : ¬(recordGapCenter + 534426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 534426]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08925_not_prime : ¬(recordGapCenter + 534516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 534516]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08926_not_prime : ¬(recordGapCenter + 534518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 534518]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08927_not_prime : ¬(recordGapCenter + 534542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 534542]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08928_not_prime : ¬(recordGapCenter + 534600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 534600]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08929_not_prime : ¬(recordGapCenter + 534642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 534642]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08930_not_prime : ¬(recordGapCenter + 534782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 534782]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08931_not_prime : ¬(recordGapCenter + 534822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 534822]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08932_not_prime : ¬(recordGapCenter + 534902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 534902]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08933_not_prime : ¬(recordGapCenter + 534938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 534938]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08934_not_prime : ¬(recordGapCenter + 534962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 534962]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08935_not_prime : ¬(recordGapCenter + 535070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535070]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08936_not_prime : ¬(recordGapCenter + 535076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535076]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08937_not_prime : ¬(recordGapCenter + 535202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535202]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08938_not_prime : ¬(recordGapCenter + 535286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535286]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08939_not_prime : ¬(recordGapCenter + 535362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535362]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08940_not_prime : ¬(recordGapCenter + 535386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535386]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08941_not_prime : ¬(recordGapCenter + 535442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535442]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08942_not_prime : ¬(recordGapCenter + 535452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535452]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08943_not_prime : ¬(recordGapCenter + 535566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535566]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08944_not_prime : ¬(recordGapCenter + 535592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535592]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08945_not_prime : ¬(recordGapCenter + 535802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535802]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08946_not_prime : ¬(recordGapCenter + 535812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535812]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08947_not_prime : ¬(recordGapCenter + 535818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535818]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08948_not_prime : ¬(recordGapCenter + 535826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535826]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08949_not_prime : ¬(recordGapCenter + 535910).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 535910]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08950_not_prime : ¬(recordGapCenter + 536006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536006]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08951_not_prime : ¬(recordGapCenter + 536126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536126]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08952_not_prime : ¬(recordGapCenter + 536138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536138]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08953_not_prime : ¬(recordGapCenter + 536168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536168]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08954_not_prime : ¬(recordGapCenter + 536196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536196]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08955_not_prime : ¬(recordGapCenter + 536226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536226]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08956_not_prime : ¬(recordGapCenter + 536286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536286]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08957_not_prime : ¬(recordGapCenter + 536306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536306]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08958_not_prime : ¬(recordGapCenter + 536342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536342]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08959_not_prime : ¬(recordGapCenter + 536348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536348]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

theorem fullRecordGapTerm08960_not_prime : ¬(recordGapCenter + 536372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 536372]
  · apply fullRecordGapRow00140_fermat
    simp [fullRecordGapRow00140_values]

end PrimeFactorUnimodality
