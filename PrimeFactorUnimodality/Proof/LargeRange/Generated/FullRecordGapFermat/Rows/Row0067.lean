import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00067_values : List Nat :=
  [fullRecordGapCenterValue + 111266,
    fullRecordGapCenterValue + 111326,
    fullRecordGapCenterValue + 111638,
    fullRecordGapCenterValue + 111686,
    fullRecordGapCenterValue + 112640,
    fullRecordGapCenterValue + 112946,
    fullRecordGapCenterValue + 113006,
    fullRecordGapCenterValue + 113018,
    fullRecordGapCenterValue + 113222,
    fullRecordGapCenterValue + 113402,
    fullRecordGapCenterValue + 113642,
    fullRecordGapCenterValue + 113858,
    fullRecordGapCenterValue + 114326,
    fullRecordGapCenterValue + 114446,
    fullRecordGapCenterValue + 114566,
    fullRecordGapCenterValue + 114698,
    fullRecordGapCenterValue + 115118,
    fullRecordGapCenterValue + 115200,
    fullRecordGapCenterValue + 115418,
    fullRecordGapCenterValue + 115586,
    fullRecordGapCenterValue + 115658,
    fullRecordGapCenterValue + 115802,
    fullRecordGapCenterValue + 115886,
    fullRecordGapCenterValue + 116342,
    fullRecordGapCenterValue + 116462,
    fullRecordGapCenterValue + 116642,
    fullRecordGapCenterValue + 116786,
    fullRecordGapCenterValue + 117206,
    fullRecordGapCenterValue + 117398,
    fullRecordGapCenterValue + 117422,
    fullRecordGapCenterValue + 117482,
    fullRecordGapCenterValue + 117926,
    fullRecordGapCenterValue + 118022,
    fullRecordGapCenterValue + 118238,
    fullRecordGapCenterValue + 118272,
    fullRecordGapCenterValue + 118442,
    fullRecordGapCenterValue + 118580,
    fullRecordGapCenterValue + 118886,
    fullRecordGapCenterValue + 119070,
    fullRecordGapCenterValue + 119162,
    fullRecordGapCenterValue + 119222,
    fullRecordGapCenterValue + 119486,
    fullRecordGapCenterValue + 119582,
    fullRecordGapCenterValue + 119618,
    fullRecordGapCenterValue + 119726,
    fullRecordGapCenterValue + 120026,
    fullRecordGapCenterValue + 120338,
    fullRecordGapCenterValue + 120960,
    fullRecordGapCenterValue + 121202,
    fullRecordGapCenterValue + 121262,
    fullRecordGapCenterValue + 121298,
    fullRecordGapCenterValue + 121466,
    fullRecordGapCenterValue + 121718,
    fullRecordGapCenterValue + 121826,
    fullRecordGapCenterValue + 121968,
    fullRecordGapCenterValue + 122102,
    fullRecordGapCenterValue + 122306,
    fullRecordGapCenterValue + 122462,
    fullRecordGapCenterValue + 122882,
    fullRecordGapCenterValue + 123200,
    fullRecordGapCenterValue + 123362,
    fullRecordGapCenterValue + 123446,
    fullRecordGapCenterValue + 123638,
    fullRecordGapCenterValue + 123686]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00067_fermat : ∀ n ∈ fullRecordGapRow00067_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04225_not_prime : ¬(recordGapCenter + 111266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 111266]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04226_not_prime : ¬(recordGapCenter + 111326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 111326]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04227_not_prime : ¬(recordGapCenter + 111638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 111638]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04228_not_prime : ¬(recordGapCenter + 111686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 111686]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04229_not_prime : ¬(recordGapCenter + 112640).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 112640]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04230_not_prime : ¬(recordGapCenter + 112946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 112946]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04231_not_prime : ¬(recordGapCenter + 113006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 113006]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04232_not_prime : ¬(recordGapCenter + 113018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 113018]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04233_not_prime : ¬(recordGapCenter + 113222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 113222]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04234_not_prime : ¬(recordGapCenter + 113402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 113402]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04235_not_prime : ¬(recordGapCenter + 113642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 113642]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04236_not_prime : ¬(recordGapCenter + 113858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 113858]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04237_not_prime : ¬(recordGapCenter + 114326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 114326]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04238_not_prime : ¬(recordGapCenter + 114446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 114446]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04239_not_prime : ¬(recordGapCenter + 114566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 114566]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04240_not_prime : ¬(recordGapCenter + 114698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 114698]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04241_not_prime : ¬(recordGapCenter + 115118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 115118]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04242_not_prime : ¬(recordGapCenter + 115200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 115200]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04243_not_prime : ¬(recordGapCenter + 115418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 115418]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04244_not_prime : ¬(recordGapCenter + 115586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 115586]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04245_not_prime : ¬(recordGapCenter + 115658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 115658]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04246_not_prime : ¬(recordGapCenter + 115802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 115802]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04247_not_prime : ¬(recordGapCenter + 115886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 115886]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04248_not_prime : ¬(recordGapCenter + 116342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 116342]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04249_not_prime : ¬(recordGapCenter + 116462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 116462]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04250_not_prime : ¬(recordGapCenter + 116642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 116642]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04251_not_prime : ¬(recordGapCenter + 116786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 116786]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04252_not_prime : ¬(recordGapCenter + 117206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 117206]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04253_not_prime : ¬(recordGapCenter + 117398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 117398]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04254_not_prime : ¬(recordGapCenter + 117422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 117422]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04255_not_prime : ¬(recordGapCenter + 117482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 117482]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04256_not_prime : ¬(recordGapCenter + 117926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 117926]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04257_not_prime : ¬(recordGapCenter + 118022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 118022]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04258_not_prime : ¬(recordGapCenter + 118238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 118238]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04259_not_prime : ¬(recordGapCenter + 118272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 118272]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04260_not_prime : ¬(recordGapCenter + 118442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 118442]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04261_not_prime : ¬(recordGapCenter + 118580).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 118580]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04262_not_prime : ¬(recordGapCenter + 118886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 118886]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04263_not_prime : ¬(recordGapCenter + 119070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 119070]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04264_not_prime : ¬(recordGapCenter + 119162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 119162]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04265_not_prime : ¬(recordGapCenter + 119222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 119222]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04266_not_prime : ¬(recordGapCenter + 119486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 119486]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04267_not_prime : ¬(recordGapCenter + 119582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 119582]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04268_not_prime : ¬(recordGapCenter + 119618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 119618]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04269_not_prime : ¬(recordGapCenter + 119726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 119726]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04270_not_prime : ¬(recordGapCenter + 120026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 120026]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04271_not_prime : ¬(recordGapCenter + 120338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 120338]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04272_not_prime : ¬(recordGapCenter + 120960).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 120960]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04273_not_prime : ¬(recordGapCenter + 121202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 121202]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04274_not_prime : ¬(recordGapCenter + 121262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 121262]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04275_not_prime : ¬(recordGapCenter + 121298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 121298]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04276_not_prime : ¬(recordGapCenter + 121466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 121466]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04277_not_prime : ¬(recordGapCenter + 121718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 121718]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04278_not_prime : ¬(recordGapCenter + 121826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 121826]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04279_not_prime : ¬(recordGapCenter + 121968).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 121968]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04280_not_prime : ¬(recordGapCenter + 122102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 122102]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04281_not_prime : ¬(recordGapCenter + 122306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 122306]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04282_not_prime : ¬(recordGapCenter + 122462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 122462]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04283_not_prime : ¬(recordGapCenter + 122882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 122882]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04284_not_prime : ¬(recordGapCenter + 123200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123200]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04285_not_prime : ¬(recordGapCenter + 123362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123362]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04286_not_prime : ¬(recordGapCenter + 123446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123446]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04287_not_prime : ¬(recordGapCenter + 123638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123638]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

theorem fullRecordGapTerm04288_not_prime : ¬(recordGapCenter + 123686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123686]
  · apply fullRecordGapRow00067_fermat
    simp [fullRecordGapRow00067_values]

end PrimeFactorUnimodality
