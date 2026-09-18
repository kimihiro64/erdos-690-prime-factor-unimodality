import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00078_values : List Nat :=
  [fullRecordGapCenterValue + 215426,
    fullRecordGapCenterValue + 215546,
    fullRecordGapCenterValue + 215582,
    fullRecordGapCenterValue + 215588,
    fullRecordGapCenterValue + 215678,
    fullRecordGapCenterValue + 215756,
    fullRecordGapCenterValue + 215972,
    fullRecordGapCenterValue + 216158,
    fullRecordGapCenterValue + 216422,
    fullRecordGapCenterValue + 216602,
    fullRecordGapCenterValue + 216668,
    fullRecordGapCenterValue + 216758,
    fullRecordGapCenterValue + 216842,
    fullRecordGapCenterValue + 216926,
    fullRecordGapCenterValue + 216998,
    fullRecordGapCenterValue + 217082,
    fullRecordGapCenterValue + 217106,
    fullRecordGapCenterValue + 217148,
    fullRecordGapCenterValue + 217262,
    fullRecordGapCenterValue + 217292,
    fullRecordGapCenterValue + 217298,
    fullRecordGapCenterValue + 217388,
    fullRecordGapCenterValue + 217418,
    fullRecordGapCenterValue + 217502,
    fullRecordGapCenterValue + 217886,
    fullRecordGapCenterValue + 217922,
    fullRecordGapCenterValue + 217982,
    fullRecordGapCenterValue + 217988,
    fullRecordGapCenterValue + 218468,
    fullRecordGapCenterValue + 218516,
    fullRecordGapCenterValue + 218642,
    fullRecordGapCenterValue + 218726,
    fullRecordGapCenterValue + 218750,
    fullRecordGapCenterValue + 218906,
    fullRecordGapCenterValue + 219068,
    fullRecordGapCenterValue + 219278,
    fullRecordGapCenterValue + 219662,
    fullRecordGapCenterValue + 219698,
    fullRecordGapCenterValue + 220118,
    fullRecordGapCenterValue + 220316,
    fullRecordGapCenterValue + 220322,
    fullRecordGapCenterValue + 220412,
    fullRecordGapCenterValue + 220538,
    fullRecordGapCenterValue + 220622,
    fullRecordGapCenterValue + 220652,
    fullRecordGapCenterValue + 220862,
    fullRecordGapCenterValue + 220958,
    fullRecordGapCenterValue + 221006,
    fullRecordGapCenterValue + 221036,
    fullRecordGapCenterValue + 221126,
    fullRecordGapCenterValue + 221138,
    fullRecordGapCenterValue + 221252,
    fullRecordGapCenterValue + 221258,
    fullRecordGapCenterValue + 221348,
    fullRecordGapCenterValue + 221498,
    fullRecordGapCenterValue + 221642,
    fullRecordGapCenterValue + 221726,
    fullRecordGapCenterValue + 221978,
    fullRecordGapCenterValue + 222098,
    fullRecordGapCenterValue + 222188,
    fullRecordGapCenterValue + 222206,
    fullRecordGapCenterValue + 222458,
    fullRecordGapCenterValue + 222476,
    fullRecordGapCenterValue + 222506]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00078_fermat : ∀ n ∈ fullRecordGapRow00078_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04929_not_prime : ¬(recordGapCenter + 215426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 215426]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04930_not_prime : ¬(recordGapCenter + 215546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 215546]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04931_not_prime : ¬(recordGapCenter + 215582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 215582]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04932_not_prime : ¬(recordGapCenter + 215588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 215588]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04933_not_prime : ¬(recordGapCenter + 215678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 215678]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04934_not_prime : ¬(recordGapCenter + 215756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 215756]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04935_not_prime : ¬(recordGapCenter + 215972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 215972]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04936_not_prime : ¬(recordGapCenter + 216158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 216158]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04937_not_prime : ¬(recordGapCenter + 216422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 216422]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04938_not_prime : ¬(recordGapCenter + 216602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 216602]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04939_not_prime : ¬(recordGapCenter + 216668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 216668]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04940_not_prime : ¬(recordGapCenter + 216758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 216758]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04941_not_prime : ¬(recordGapCenter + 216842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 216842]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04942_not_prime : ¬(recordGapCenter + 216926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 216926]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04943_not_prime : ¬(recordGapCenter + 216998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 216998]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04944_not_prime : ¬(recordGapCenter + 217082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 217082]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04945_not_prime : ¬(recordGapCenter + 217106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 217106]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04946_not_prime : ¬(recordGapCenter + 217148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 217148]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04947_not_prime : ¬(recordGapCenter + 217262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 217262]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04948_not_prime : ¬(recordGapCenter + 217292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 217292]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04949_not_prime : ¬(recordGapCenter + 217298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 217298]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04950_not_prime : ¬(recordGapCenter + 217388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 217388]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04951_not_prime : ¬(recordGapCenter + 217418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 217418]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04952_not_prime : ¬(recordGapCenter + 217502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 217502]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04953_not_prime : ¬(recordGapCenter + 217886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 217886]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04954_not_prime : ¬(recordGapCenter + 217922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 217922]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04955_not_prime : ¬(recordGapCenter + 217982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 217982]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04956_not_prime : ¬(recordGapCenter + 217988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 217988]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04957_not_prime : ¬(recordGapCenter + 218468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 218468]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04958_not_prime : ¬(recordGapCenter + 218516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 218516]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04959_not_prime : ¬(recordGapCenter + 218642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 218642]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04960_not_prime : ¬(recordGapCenter + 218726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 218726]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04961_not_prime : ¬(recordGapCenter + 218750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 218750]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04962_not_prime : ¬(recordGapCenter + 218906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 218906]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04963_not_prime : ¬(recordGapCenter + 219068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 219068]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04964_not_prime : ¬(recordGapCenter + 219278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 219278]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04965_not_prime : ¬(recordGapCenter + 219662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 219662]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04966_not_prime : ¬(recordGapCenter + 219698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 219698]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04967_not_prime : ¬(recordGapCenter + 220118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 220118]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04968_not_prime : ¬(recordGapCenter + 220316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 220316]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04969_not_prime : ¬(recordGapCenter + 220322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 220322]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04970_not_prime : ¬(recordGapCenter + 220412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 220412]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04971_not_prime : ¬(recordGapCenter + 220538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 220538]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04972_not_prime : ¬(recordGapCenter + 220622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 220622]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04973_not_prime : ¬(recordGapCenter + 220652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 220652]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04974_not_prime : ¬(recordGapCenter + 220862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 220862]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04975_not_prime : ¬(recordGapCenter + 220958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 220958]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04976_not_prime : ¬(recordGapCenter + 221006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 221006]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04977_not_prime : ¬(recordGapCenter + 221036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 221036]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04978_not_prime : ¬(recordGapCenter + 221126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 221126]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04979_not_prime : ¬(recordGapCenter + 221138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 221138]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04980_not_prime : ¬(recordGapCenter + 221252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 221252]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04981_not_prime : ¬(recordGapCenter + 221258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 221258]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04982_not_prime : ¬(recordGapCenter + 221348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 221348]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04983_not_prime : ¬(recordGapCenter + 221498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 221498]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04984_not_prime : ¬(recordGapCenter + 221642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 221642]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04985_not_prime : ¬(recordGapCenter + 221726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 221726]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04986_not_prime : ¬(recordGapCenter + 221978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 221978]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04987_not_prime : ¬(recordGapCenter + 222098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 222098]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04988_not_prime : ¬(recordGapCenter + 222188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 222188]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04989_not_prime : ¬(recordGapCenter + 222206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 222206]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04990_not_prime : ¬(recordGapCenter + 222458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 222458]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04991_not_prime : ¬(recordGapCenter + 222476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 222476]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

theorem fullRecordGapTerm04992_not_prime : ¬(recordGapCenter + 222506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 222506]
  · apply fullRecordGapRow00078_fermat
    simp [fullRecordGapRow00078_values]

end PrimeFactorUnimodality
