import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00017_values : List Nat :=
  [fullRecordGapCenterValue + 91682,
    fullRecordGapCenterValue + 92102,
    fullRecordGapCenterValue + 92160,
    fullRecordGapCenterValue + 92186,
    fullRecordGapCenterValue + 92282,
    fullRecordGapCenterValue + 92366,
    fullRecordGapCenterValue + 92400,
    fullRecordGapCenterValue + 92522,
    fullRecordGapCenterValue + 92610,
    fullRecordGapCenterValue + 92618,
    fullRecordGapCenterValue + 92762,
    fullRecordGapCenterValue + 92928,
    fullRecordGapCenterValue + 92942,
    fullRecordGapCenterValue + 92978,
    fullRecordGapCenterValue + 93170,
    fullRecordGapCenterValue + 93182,
    fullRecordGapCenterValue + 93278,
    fullRecordGapCenterValue + 93446,
    fullRecordGapCenterValue + 93542,
    fullRecordGapCenterValue + 93662,
    fullRecordGapCenterValue + 93866,
    fullRecordGapCenterValue + 94080,
    fullRecordGapCenterValue + 94286,
    fullRecordGapCenterValue + 94298,
    fullRecordGapCenterValue + 94538,
    fullRecordGapCenterValue + 94586,
    fullRecordGapCenterValue + 95040,
    fullRecordGapCenterValue + 95126,
    fullRecordGapCenterValue + 95138,
    fullRecordGapCenterValue + 95258,
    fullRecordGapCenterValue + 95558,
    fullRecordGapCenterValue + 95582,
    fullRecordGapCenterValue + 96098,
    fullRecordGapCenterValue + 96626,
    fullRecordGapCenterValue + 96800,
    fullRecordGapCenterValue + 96962,
    fullRecordGapCenterValue + 97046,
    fullRecordGapCenterValue + 97178,
    fullRecordGapCenterValue + 97200,
    fullRecordGapCenterValue + 97238,
    fullRecordGapCenterValue + 97322,
    fullRecordGapCenterValue + 97358,
    fullRecordGapCenterValue + 97466,
    fullRecordGapCenterValue + 97718,
    fullRecordGapCenterValue + 97766,
    fullRecordGapCenterValue + 97946,
    fullRecordGapCenterValue + 98066,
    fullRecordGapCenterValue + 98246,
    fullRecordGapCenterValue + 98522,
    fullRecordGapCenterValue + 98558,
    fullRecordGapCenterValue + 98786,
    fullRecordGapCenterValue + 98858,
    fullRecordGapCenterValue + 98918,
    fullRecordGapCenterValue + 99206,
    fullRecordGapCenterValue + 99278,
    fullRecordGapCenterValue + 99842,
    fullRecordGapCenterValue + 100046,
    fullRecordGapCenterValue + 100238,
    fullRecordGapCenterValue + 100352,
    fullRecordGapCenterValue + 100658,
    fullRecordGapCenterValue + 101162,
    fullRecordGapCenterValue + 101186,
    fullRecordGapCenterValue + 101342,
    fullRecordGapCenterValue + 101546,
    fullRecordGapCenterValue + 101846,
    fullRecordGapCenterValue + 102482,
    fullRecordGapCenterValue + 102686,
    fullRecordGapCenterValue + 102842,
    fullRecordGapCenterValue + 102900,
    fullRecordGapCenterValue + 103226,
    fullRecordGapCenterValue + 103346,
    fullRecordGapCenterValue + 103538,
    fullRecordGapCenterValue + 103826,
    fullRecordGapCenterValue + 103950,
    fullRecordGapCenterValue + 103982,
    fullRecordGapCenterValue + 104018,
    fullRecordGapCenterValue + 104042,
    fullRecordGapCenterValue + 104102,
    fullRecordGapCenterValue + 104402,
    fullRecordGapCenterValue + 104498,
    fullRecordGapCenterValue + 104906,
    fullRecordGapCenterValue + 105000,
    fullRecordGapCenterValue + 105086,
    fullRecordGapCenterValue + 105158,
    fullRecordGapCenterValue + 105218,
    fullRecordGapCenterValue + 105600,
    fullRecordGapCenterValue + 105626,
    fullRecordGapCenterValue + 105722,
    fullRecordGapCenterValue + 105758,
    fullRecordGapCenterValue + 105840,
    fullRecordGapCenterValue + 106178,
    fullRecordGapCenterValue + 106562,
    fullRecordGapCenterValue + 106598,
    fullRecordGapCenterValue + 106802,
    fullRecordGapCenterValue + 106838,
    fullRecordGapCenterValue + 106920,
    fullRecordGapCenterValue + 107006,
    fullRecordGapCenterValue + 107102,
    fullRecordGapCenterValue + 107138,
    fullRecordGapCenterValue + 107258,
    fullRecordGapCenterValue + 107520,
    fullRecordGapCenterValue + 107798,
    fullRecordGapCenterValue + 107846,
    fullRecordGapCenterValue + 108000,
    fullRecordGapCenterValue + 108182,
    fullRecordGapCenterValue + 108242,
    fullRecordGapCenterValue + 108266,
    fullRecordGapCenterValue + 108278,
    fullRecordGapCenterValue + 108326,
    fullRecordGapCenterValue + 108362,
    fullRecordGapCenterValue + 108638,
    fullRecordGapCenterValue + 108662,
    fullRecordGapCenterValue + 108722,
    fullRecordGapCenterValue + 108938,
    fullRecordGapCenterValue + 108986,
    fullRecordGapCenterValue + 109082,
    fullRecordGapCenterValue + 109118,
    fullRecordGapCenterValue + 109166,
    fullRecordGapCenterValue + 109202,
    fullRecordGapCenterValue + 109350,
    fullRecordGapCenterValue + 109658,
    fullRecordGapCenterValue + 109898,
    fullRecordGapCenterValue + 109946,
    fullRecordGapCenterValue + 110426,
    fullRecordGapCenterValue + 110486,
    fullRecordGapCenterValue + 110498,
    fullRecordGapCenterValue + 110666,
    fullRecordGapCenterValue + 110798,
    fullRecordGapCenterValue + 111266,
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
    fullRecordGapCenterValue + 123686,
    fullRecordGapCenterValue + 123722,
    fullRecordGapCenterValue + 123750,
    fullRecordGapCenterValue + 123866,
    fullRecordGapCenterValue + 124022,
    fullRecordGapCenterValue + 124416,
    fullRecordGapCenterValue + 124740,
    fullRecordGapCenterValue + 124766,
    fullRecordGapCenterValue + 125078,
    fullRecordGapCenterValue + 125402,
    fullRecordGapCenterValue + 125486,
    fullRecordGapCenterValue + 125546,
    fullRecordGapCenterValue + 125582,
    fullRecordGapCenterValue + 125738,
    fullRecordGapCenterValue + 125966,
    fullRecordGapCenterValue + 126158,
    fullRecordGapCenterValue + 126662,
    fullRecordGapCenterValue + 126722,
    fullRecordGapCenterValue + 126842,
    fullRecordGapCenterValue + 126878,
    fullRecordGapCenterValue + 127008,
    fullRecordGapCenterValue + 127082,
    fullRecordGapCenterValue + 127118,
    fullRecordGapCenterValue + 127202,
    fullRecordGapCenterValue + 127776,
    fullRecordGapCenterValue + 127898,
    fullRecordGapCenterValue + 128306,
    fullRecordGapCenterValue + 128462,
    fullRecordGapCenterValue + 128606,
    fullRecordGapCenterValue + 128798,
    fullRecordGapCenterValue + 129266,
    fullRecordGapCenterValue + 129326,
    fullRecordGapCenterValue + 129360,
    fullRecordGapCenterValue + 129386,
    fullRecordGapCenterValue + 129566,
    fullRecordGapCenterValue + 129782,
    fullRecordGapCenterValue + 130022,
    fullRecordGapCenterValue + 130106,
    fullRecordGapCenterValue + 130142,
    fullRecordGapCenterValue + 130238,
    fullRecordGapCenterValue + 130406,
    fullRecordGapCenterValue + 130538,
    fullRecordGapCenterValue + 130646,
    fullRecordGapCenterValue + 130706,
    fullRecordGapCenterValue + 130826,
    fullRecordGapCenterValue + 131198,
    fullRecordGapCenterValue + 131220,
    fullRecordGapCenterValue + 131678,
    fullRecordGapCenterValue + 131702,
    fullRecordGapCenterValue + 131966,
    fullRecordGapCenterValue + 132338,
    fullRecordGapCenterValue + 132602,
    fullRecordGapCenterValue + 132686,
    fullRecordGapCenterValue + 132746,
    fullRecordGapCenterValue + 132926,
    fullRecordGapCenterValue + 132998,
    fullRecordGapCenterValue + 133056,
    fullRecordGapCenterValue + 133058,
    fullRecordGapCenterValue + 133106,
    fullRecordGapCenterValue + 133466,
    fullRecordGapCenterValue + 133478,
    fullRecordGapCenterValue + 133526,
    fullRecordGapCenterValue + 133682,
    fullRecordGapCenterValue + 134258,
    fullRecordGapCenterValue + 134750]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00017_fermat : ∀ n ∈ fullRecordGapRow00017_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04097_not_prime : ¬(recordGapCenter + 91682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 91682]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04098_not_prime : ¬(recordGapCenter + 92102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92102]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04099_not_prime : ¬(recordGapCenter + 92160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92160]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04100_not_prime : ¬(recordGapCenter + 92186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92186]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04101_not_prime : ¬(recordGapCenter + 92282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92282]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04102_not_prime : ¬(recordGapCenter + 92366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92366]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04103_not_prime : ¬(recordGapCenter + 92400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92400]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04104_not_prime : ¬(recordGapCenter + 92522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92522]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04105_not_prime : ¬(recordGapCenter + 92610).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92610]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04106_not_prime : ¬(recordGapCenter + 92618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92618]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04107_not_prime : ¬(recordGapCenter + 92762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92762]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04108_not_prime : ¬(recordGapCenter + 92928).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92928]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04109_not_prime : ¬(recordGapCenter + 92942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92942]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04110_not_prime : ¬(recordGapCenter + 92978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 92978]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04111_not_prime : ¬(recordGapCenter + 93170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 93170]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04112_not_prime : ¬(recordGapCenter + 93182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 93182]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04113_not_prime : ¬(recordGapCenter + 93278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 93278]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04114_not_prime : ¬(recordGapCenter + 93446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 93446]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04115_not_prime : ¬(recordGapCenter + 93542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 93542]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04116_not_prime : ¬(recordGapCenter + 93662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 93662]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04117_not_prime : ¬(recordGapCenter + 93866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 93866]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04118_not_prime : ¬(recordGapCenter + 94080).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 94080]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04119_not_prime : ¬(recordGapCenter + 94286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 94286]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04120_not_prime : ¬(recordGapCenter + 94298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 94298]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04121_not_prime : ¬(recordGapCenter + 94538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 94538]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04122_not_prime : ¬(recordGapCenter + 94586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 94586]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04123_not_prime : ¬(recordGapCenter + 95040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 95040]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04124_not_prime : ¬(recordGapCenter + 95126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 95126]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04125_not_prime : ¬(recordGapCenter + 95138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 95138]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04126_not_prime : ¬(recordGapCenter + 95258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 95258]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04127_not_prime : ¬(recordGapCenter + 95558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 95558]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04128_not_prime : ¬(recordGapCenter + 95582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 95582]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04129_not_prime : ¬(recordGapCenter + 96098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 96098]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04130_not_prime : ¬(recordGapCenter + 96626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 96626]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04131_not_prime : ¬(recordGapCenter + 96800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 96800]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04132_not_prime : ¬(recordGapCenter + 96962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 96962]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04133_not_prime : ¬(recordGapCenter + 97046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97046]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04134_not_prime : ¬(recordGapCenter + 97178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97178]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04135_not_prime : ¬(recordGapCenter + 97200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97200]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04136_not_prime : ¬(recordGapCenter + 97238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97238]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04137_not_prime : ¬(recordGapCenter + 97322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97322]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04138_not_prime : ¬(recordGapCenter + 97358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97358]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04139_not_prime : ¬(recordGapCenter + 97466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97466]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04140_not_prime : ¬(recordGapCenter + 97718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97718]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04141_not_prime : ¬(recordGapCenter + 97766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97766]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04142_not_prime : ¬(recordGapCenter + 97946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 97946]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04143_not_prime : ¬(recordGapCenter + 98066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 98066]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04144_not_prime : ¬(recordGapCenter + 98246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 98246]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04145_not_prime : ¬(recordGapCenter + 98522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 98522]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04146_not_prime : ¬(recordGapCenter + 98558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 98558]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04147_not_prime : ¬(recordGapCenter + 98786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 98786]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04148_not_prime : ¬(recordGapCenter + 98858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 98858]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04149_not_prime : ¬(recordGapCenter + 98918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 98918]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04150_not_prime : ¬(recordGapCenter + 99206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 99206]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04151_not_prime : ¬(recordGapCenter + 99278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 99278]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04152_not_prime : ¬(recordGapCenter + 99842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 99842]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04153_not_prime : ¬(recordGapCenter + 100046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 100046]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04154_not_prime : ¬(recordGapCenter + 100238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 100238]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04155_not_prime : ¬(recordGapCenter + 100352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 100352]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04156_not_prime : ¬(recordGapCenter + 100658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 100658]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04157_not_prime : ¬(recordGapCenter + 101162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 101162]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04158_not_prime : ¬(recordGapCenter + 101186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 101186]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04159_not_prime : ¬(recordGapCenter + 101342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 101342]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04160_not_prime : ¬(recordGapCenter + 101546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 101546]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04161_not_prime : ¬(recordGapCenter + 101846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 101846]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04162_not_prime : ¬(recordGapCenter + 102482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 102482]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04163_not_prime : ¬(recordGapCenter + 102686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 102686]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04164_not_prime : ¬(recordGapCenter + 102842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 102842]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04165_not_prime : ¬(recordGapCenter + 102900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 102900]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04166_not_prime : ¬(recordGapCenter + 103226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 103226]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04167_not_prime : ¬(recordGapCenter + 103346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 103346]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04168_not_prime : ¬(recordGapCenter + 103538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 103538]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04169_not_prime : ¬(recordGapCenter + 103826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 103826]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04170_not_prime : ¬(recordGapCenter + 103950).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 103950]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04171_not_prime : ¬(recordGapCenter + 103982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 103982]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04172_not_prime : ¬(recordGapCenter + 104018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 104018]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04173_not_prime : ¬(recordGapCenter + 104042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 104042]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04174_not_prime : ¬(recordGapCenter + 104102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 104102]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04175_not_prime : ¬(recordGapCenter + 104402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 104402]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04176_not_prime : ¬(recordGapCenter + 104498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 104498]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04177_not_prime : ¬(recordGapCenter + 104906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 104906]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04178_not_prime : ¬(recordGapCenter + 105000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105000]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04179_not_prime : ¬(recordGapCenter + 105086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105086]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04180_not_prime : ¬(recordGapCenter + 105158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105158]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04181_not_prime : ¬(recordGapCenter + 105218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105218]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04182_not_prime : ¬(recordGapCenter + 105600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105600]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04183_not_prime : ¬(recordGapCenter + 105626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105626]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04184_not_prime : ¬(recordGapCenter + 105722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105722]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04185_not_prime : ¬(recordGapCenter + 105758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105758]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04186_not_prime : ¬(recordGapCenter + 105840).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105840]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04187_not_prime : ¬(recordGapCenter + 106178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 106178]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04188_not_prime : ¬(recordGapCenter + 106562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 106562]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04189_not_prime : ¬(recordGapCenter + 106598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 106598]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04190_not_prime : ¬(recordGapCenter + 106802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 106802]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04191_not_prime : ¬(recordGapCenter + 106838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 106838]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04192_not_prime : ¬(recordGapCenter + 106920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 106920]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04193_not_prime : ¬(recordGapCenter + 107006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 107006]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04194_not_prime : ¬(recordGapCenter + 107102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 107102]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04195_not_prime : ¬(recordGapCenter + 107138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 107138]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04196_not_prime : ¬(recordGapCenter + 107258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 107258]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04197_not_prime : ¬(recordGapCenter + 107520).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 107520]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04198_not_prime : ¬(recordGapCenter + 107798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 107798]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04199_not_prime : ¬(recordGapCenter + 107846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 107846]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04200_not_prime : ¬(recordGapCenter + 108000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108000]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04201_not_prime : ¬(recordGapCenter + 108182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108182]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04202_not_prime : ¬(recordGapCenter + 108242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108242]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04203_not_prime : ¬(recordGapCenter + 108266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108266]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04204_not_prime : ¬(recordGapCenter + 108278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108278]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04205_not_prime : ¬(recordGapCenter + 108326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108326]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04206_not_prime : ¬(recordGapCenter + 108362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108362]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04207_not_prime : ¬(recordGapCenter + 108638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108638]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04208_not_prime : ¬(recordGapCenter + 108662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108662]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04209_not_prime : ¬(recordGapCenter + 108722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108722]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04210_not_prime : ¬(recordGapCenter + 108938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108938]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04211_not_prime : ¬(recordGapCenter + 108986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108986]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04212_not_prime : ¬(recordGapCenter + 109082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109082]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04213_not_prime : ¬(recordGapCenter + 109118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109118]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04214_not_prime : ¬(recordGapCenter + 109166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109166]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04215_not_prime : ¬(recordGapCenter + 109202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109202]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04216_not_prime : ¬(recordGapCenter + 109350).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109350]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04217_not_prime : ¬(recordGapCenter + 109658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109658]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04218_not_prime : ¬(recordGapCenter + 109898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109898]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04219_not_prime : ¬(recordGapCenter + 109946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109946]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04220_not_prime : ¬(recordGapCenter + 110426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 110426]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04221_not_prime : ¬(recordGapCenter + 110486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 110486]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04222_not_prime : ¬(recordGapCenter + 110498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 110498]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04223_not_prime : ¬(recordGapCenter + 110666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 110666]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04224_not_prime : ¬(recordGapCenter + 110798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 110798]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04225_not_prime : ¬(recordGapCenter + 111266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 111266]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04226_not_prime : ¬(recordGapCenter + 111326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 111326]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04227_not_prime : ¬(recordGapCenter + 111638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 111638]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04228_not_prime : ¬(recordGapCenter + 111686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 111686]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04229_not_prime : ¬(recordGapCenter + 112640).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 112640]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04230_not_prime : ¬(recordGapCenter + 112946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 112946]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04231_not_prime : ¬(recordGapCenter + 113006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 113006]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04232_not_prime : ¬(recordGapCenter + 113018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 113018]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04233_not_prime : ¬(recordGapCenter + 113222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 113222]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04234_not_prime : ¬(recordGapCenter + 113402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 113402]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04235_not_prime : ¬(recordGapCenter + 113642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 113642]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04236_not_prime : ¬(recordGapCenter + 113858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 113858]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04237_not_prime : ¬(recordGapCenter + 114326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 114326]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04238_not_prime : ¬(recordGapCenter + 114446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 114446]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04239_not_prime : ¬(recordGapCenter + 114566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 114566]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04240_not_prime : ¬(recordGapCenter + 114698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 114698]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04241_not_prime : ¬(recordGapCenter + 115118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 115118]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04242_not_prime : ¬(recordGapCenter + 115200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 115200]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04243_not_prime : ¬(recordGapCenter + 115418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 115418]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04244_not_prime : ¬(recordGapCenter + 115586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 115586]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04245_not_prime : ¬(recordGapCenter + 115658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 115658]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04246_not_prime : ¬(recordGapCenter + 115802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 115802]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04247_not_prime : ¬(recordGapCenter + 115886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 115886]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04248_not_prime : ¬(recordGapCenter + 116342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 116342]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04249_not_prime : ¬(recordGapCenter + 116462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 116462]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04250_not_prime : ¬(recordGapCenter + 116642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 116642]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04251_not_prime : ¬(recordGapCenter + 116786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 116786]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04252_not_prime : ¬(recordGapCenter + 117206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 117206]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04253_not_prime : ¬(recordGapCenter + 117398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 117398]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04254_not_prime : ¬(recordGapCenter + 117422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 117422]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04255_not_prime : ¬(recordGapCenter + 117482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 117482]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04256_not_prime : ¬(recordGapCenter + 117926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 117926]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04257_not_prime : ¬(recordGapCenter + 118022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 118022]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04258_not_prime : ¬(recordGapCenter + 118238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 118238]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04259_not_prime : ¬(recordGapCenter + 118272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 118272]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04260_not_prime : ¬(recordGapCenter + 118442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 118442]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04261_not_prime : ¬(recordGapCenter + 118580).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 118580]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04262_not_prime : ¬(recordGapCenter + 118886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 118886]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04263_not_prime : ¬(recordGapCenter + 119070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 119070]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04264_not_prime : ¬(recordGapCenter + 119162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 119162]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04265_not_prime : ¬(recordGapCenter + 119222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 119222]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04266_not_prime : ¬(recordGapCenter + 119486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 119486]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04267_not_prime : ¬(recordGapCenter + 119582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 119582]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04268_not_prime : ¬(recordGapCenter + 119618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 119618]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04269_not_prime : ¬(recordGapCenter + 119726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 119726]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04270_not_prime : ¬(recordGapCenter + 120026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 120026]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04271_not_prime : ¬(recordGapCenter + 120338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 120338]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04272_not_prime : ¬(recordGapCenter + 120960).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 120960]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04273_not_prime : ¬(recordGapCenter + 121202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 121202]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04274_not_prime : ¬(recordGapCenter + 121262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 121262]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04275_not_prime : ¬(recordGapCenter + 121298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 121298]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04276_not_prime : ¬(recordGapCenter + 121466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 121466]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04277_not_prime : ¬(recordGapCenter + 121718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 121718]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04278_not_prime : ¬(recordGapCenter + 121826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 121826]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04279_not_prime : ¬(recordGapCenter + 121968).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 121968]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04280_not_prime : ¬(recordGapCenter + 122102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 122102]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04281_not_prime : ¬(recordGapCenter + 122306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 122306]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04282_not_prime : ¬(recordGapCenter + 122462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 122462]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04283_not_prime : ¬(recordGapCenter + 122882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 122882]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04284_not_prime : ¬(recordGapCenter + 123200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123200]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04285_not_prime : ¬(recordGapCenter + 123362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123362]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04286_not_prime : ¬(recordGapCenter + 123446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123446]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04287_not_prime : ¬(recordGapCenter + 123638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123638]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04288_not_prime : ¬(recordGapCenter + 123686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123686]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04289_not_prime : ¬(recordGapCenter + 123722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123722]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04290_not_prime : ¬(recordGapCenter + 123750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123750]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04291_not_prime : ¬(recordGapCenter + 123866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123866]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04292_not_prime : ¬(recordGapCenter + 124022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 124022]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04293_not_prime : ¬(recordGapCenter + 124416).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 124416]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04294_not_prime : ¬(recordGapCenter + 124740).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 124740]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04295_not_prime : ¬(recordGapCenter + 124766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 124766]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04296_not_prime : ¬(recordGapCenter + 125078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 125078]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04297_not_prime : ¬(recordGapCenter + 125402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 125402]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04298_not_prime : ¬(recordGapCenter + 125486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 125486]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04299_not_prime : ¬(recordGapCenter + 125546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 125546]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04300_not_prime : ¬(recordGapCenter + 125582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 125582]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04301_not_prime : ¬(recordGapCenter + 125738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 125738]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04302_not_prime : ¬(recordGapCenter + 125966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 125966]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04303_not_prime : ¬(recordGapCenter + 126158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 126158]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04304_not_prime : ¬(recordGapCenter + 126662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 126662]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04305_not_prime : ¬(recordGapCenter + 126722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 126722]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04306_not_prime : ¬(recordGapCenter + 126842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 126842]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04307_not_prime : ¬(recordGapCenter + 126878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 126878]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04308_not_prime : ¬(recordGapCenter + 127008).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 127008]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04309_not_prime : ¬(recordGapCenter + 127082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 127082]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04310_not_prime : ¬(recordGapCenter + 127118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 127118]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04311_not_prime : ¬(recordGapCenter + 127202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 127202]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04312_not_prime : ¬(recordGapCenter + 127776).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 127776]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04313_not_prime : ¬(recordGapCenter + 127898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 127898]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04314_not_prime : ¬(recordGapCenter + 128306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 128306]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04315_not_prime : ¬(recordGapCenter + 128462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 128462]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04316_not_prime : ¬(recordGapCenter + 128606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 128606]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04317_not_prime : ¬(recordGapCenter + 128798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 128798]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04318_not_prime : ¬(recordGapCenter + 129266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 129266]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04319_not_prime : ¬(recordGapCenter + 129326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 129326]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04320_not_prime : ¬(recordGapCenter + 129360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 129360]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04321_not_prime : ¬(recordGapCenter + 129386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 129386]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04322_not_prime : ¬(recordGapCenter + 129566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 129566]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04323_not_prime : ¬(recordGapCenter + 129782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 129782]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04324_not_prime : ¬(recordGapCenter + 130022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130022]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04325_not_prime : ¬(recordGapCenter + 130106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130106]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04326_not_prime : ¬(recordGapCenter + 130142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130142]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04327_not_prime : ¬(recordGapCenter + 130238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130238]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04328_not_prime : ¬(recordGapCenter + 130406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130406]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04329_not_prime : ¬(recordGapCenter + 130538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130538]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04330_not_prime : ¬(recordGapCenter + 130646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130646]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04331_not_prime : ¬(recordGapCenter + 130706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130706]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04332_not_prime : ¬(recordGapCenter + 130826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130826]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04333_not_prime : ¬(recordGapCenter + 131198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 131198]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04334_not_prime : ¬(recordGapCenter + 131220).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 131220]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04335_not_prime : ¬(recordGapCenter + 131678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 131678]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04336_not_prime : ¬(recordGapCenter + 131702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 131702]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04337_not_prime : ¬(recordGapCenter + 131966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 131966]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04338_not_prime : ¬(recordGapCenter + 132338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 132338]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04339_not_prime : ¬(recordGapCenter + 132602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 132602]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04340_not_prime : ¬(recordGapCenter + 132686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 132686]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04341_not_prime : ¬(recordGapCenter + 132746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 132746]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04342_not_prime : ¬(recordGapCenter + 132926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 132926]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04343_not_prime : ¬(recordGapCenter + 132998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 132998]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04344_not_prime : ¬(recordGapCenter + 133056).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 133056]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04345_not_prime : ¬(recordGapCenter + 133058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 133058]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04346_not_prime : ¬(recordGapCenter + 133106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 133106]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04347_not_prime : ¬(recordGapCenter + 133466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 133466]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04348_not_prime : ¬(recordGapCenter + 133478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 133478]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04349_not_prime : ¬(recordGapCenter + 133526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 133526]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04350_not_prime : ¬(recordGapCenter + 133682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 133682]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04351_not_prime : ¬(recordGapCenter + 134258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 134258]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

theorem fullRecordGapTerm04352_not_prime : ¬(recordGapCenter + 134750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 134750]
  · apply fullRecordGapRow00017_fermat
    simp [fullRecordGapRow00017_values]

end PrimeFactorUnimodality
