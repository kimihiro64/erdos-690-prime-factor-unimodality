import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00097_values : List Nat :=
  [fullRecordGapCenterValue + 327266,
    fullRecordGapCenterValue + 327462,
    fullRecordGapCenterValue + 327482,
    fullRecordGapCenterValue + 327486,
    fullRecordGapCenterValue + 327638,
    fullRecordGapCenterValue + 327738,
    fullRecordGapCenterValue + 327786,
    fullRecordGapCenterValue + 327812,
    fullRecordGapCenterValue + 327882,
    fullRecordGapCenterValue + 327962,
    fullRecordGapCenterValue + 328022,
    fullRecordGapCenterValue + 328046,
    fullRecordGapCenterValue + 328298,
    fullRecordGapCenterValue + 328326,
    fullRecordGapCenterValue + 328466,
    fullRecordGapCenterValue + 328506,
    fullRecordGapCenterValue + 328598,
    fullRecordGapCenterValue + 328652,
    fullRecordGapCenterValue + 328722,
    fullRecordGapCenterValue + 328772,
    fullRecordGapCenterValue + 328868,
    fullRecordGapCenterValue + 328898,
    fullRecordGapCenterValue + 329228,
    fullRecordGapCenterValue + 329262,
    fullRecordGapCenterValue + 329366,
    fullRecordGapCenterValue + 329442,
    fullRecordGapCenterValue + 329502,
    fullRecordGapCenterValue + 329618,
    fullRecordGapCenterValue + 329828,
    fullRecordGapCenterValue + 329852,
    fullRecordGapCenterValue + 329876,
    fullRecordGapCenterValue + 329948,
    fullRecordGapCenterValue + 330002,
    fullRecordGapCenterValue + 330206,
    fullRecordGapCenterValue + 330306,
    fullRecordGapCenterValue + 330366,
    fullRecordGapCenterValue + 330422,
    fullRecordGapCenterValue + 330452,
    fullRecordGapCenterValue + 330626,
    fullRecordGapCenterValue + 330662,
    fullRecordGapCenterValue + 330698,
    fullRecordGapCenterValue + 330758,
    fullRecordGapCenterValue + 330782,
    fullRecordGapCenterValue + 330926,
    fullRecordGapCenterValue + 330978,
    fullRecordGapCenterValue + 331026,
    fullRecordGapCenterValue + 331082,
    fullRecordGapCenterValue + 331202,
    fullRecordGapCenterValue + 331242,
    fullRecordGapCenterValue + 331278,
    fullRecordGapCenterValue + 331346,
    fullRecordGapCenterValue + 331388,
    fullRecordGapCenterValue + 331418,
    fullRecordGapCenterValue + 331458,
    fullRecordGapCenterValue + 331532,
    fullRecordGapCenterValue + 331622,
    fullRecordGapCenterValue + 331746,
    fullRecordGapCenterValue + 331776,
    fullRecordGapCenterValue + 331986,
    fullRecordGapCenterValue + 332106,
    fullRecordGapCenterValue + 332126,
    fullRecordGapCenterValue + 332162,
    fullRecordGapCenterValue + 332252,
    fullRecordGapCenterValue + 332286]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00097_fermat : ∀ n ∈ fullRecordGapRow00097_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06145_not_prime : ¬(recordGapCenter + 327266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 327266]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06146_not_prime : ¬(recordGapCenter + 327462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 327462]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06147_not_prime : ¬(recordGapCenter + 327482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 327482]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06148_not_prime : ¬(recordGapCenter + 327486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 327486]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06149_not_prime : ¬(recordGapCenter + 327638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 327638]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06150_not_prime : ¬(recordGapCenter + 327738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 327738]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06151_not_prime : ¬(recordGapCenter + 327786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 327786]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06152_not_prime : ¬(recordGapCenter + 327812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 327812]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06153_not_prime : ¬(recordGapCenter + 327882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 327882]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06154_not_prime : ¬(recordGapCenter + 327962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 327962]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06155_not_prime : ¬(recordGapCenter + 328022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 328022]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06156_not_prime : ¬(recordGapCenter + 328046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 328046]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06157_not_prime : ¬(recordGapCenter + 328298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 328298]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06158_not_prime : ¬(recordGapCenter + 328326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 328326]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06159_not_prime : ¬(recordGapCenter + 328466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 328466]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06160_not_prime : ¬(recordGapCenter + 328506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 328506]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06161_not_prime : ¬(recordGapCenter + 328598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 328598]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06162_not_prime : ¬(recordGapCenter + 328652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 328652]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06163_not_prime : ¬(recordGapCenter + 328722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 328722]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06164_not_prime : ¬(recordGapCenter + 328772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 328772]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06165_not_prime : ¬(recordGapCenter + 328868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 328868]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06166_not_prime : ¬(recordGapCenter + 328898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 328898]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06167_not_prime : ¬(recordGapCenter + 329228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 329228]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06168_not_prime : ¬(recordGapCenter + 329262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 329262]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06169_not_prime : ¬(recordGapCenter + 329366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 329366]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06170_not_prime : ¬(recordGapCenter + 329442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 329442]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06171_not_prime : ¬(recordGapCenter + 329502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 329502]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06172_not_prime : ¬(recordGapCenter + 329618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 329618]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06173_not_prime : ¬(recordGapCenter + 329828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 329828]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06174_not_prime : ¬(recordGapCenter + 329852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 329852]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06175_not_prime : ¬(recordGapCenter + 329876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 329876]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06176_not_prime : ¬(recordGapCenter + 329948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 329948]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06177_not_prime : ¬(recordGapCenter + 330002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 330002]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06178_not_prime : ¬(recordGapCenter + 330206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 330206]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06179_not_prime : ¬(recordGapCenter + 330306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 330306]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06180_not_prime : ¬(recordGapCenter + 330366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 330366]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06181_not_prime : ¬(recordGapCenter + 330422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 330422]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06182_not_prime : ¬(recordGapCenter + 330452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 330452]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06183_not_prime : ¬(recordGapCenter + 330626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 330626]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06184_not_prime : ¬(recordGapCenter + 330662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 330662]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06185_not_prime : ¬(recordGapCenter + 330698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 330698]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06186_not_prime : ¬(recordGapCenter + 330758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 330758]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06187_not_prime : ¬(recordGapCenter + 330782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 330782]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06188_not_prime : ¬(recordGapCenter + 330926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 330926]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06189_not_prime : ¬(recordGapCenter + 330978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 330978]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06190_not_prime : ¬(recordGapCenter + 331026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 331026]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06191_not_prime : ¬(recordGapCenter + 331082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 331082]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06192_not_prime : ¬(recordGapCenter + 331202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 331202]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06193_not_prime : ¬(recordGapCenter + 331242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 331242]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06194_not_prime : ¬(recordGapCenter + 331278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 331278]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06195_not_prime : ¬(recordGapCenter + 331346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 331346]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06196_not_prime : ¬(recordGapCenter + 331388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 331388]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06197_not_prime : ¬(recordGapCenter + 331418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 331418]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06198_not_prime : ¬(recordGapCenter + 331458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 331458]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06199_not_prime : ¬(recordGapCenter + 331532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 331532]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06200_not_prime : ¬(recordGapCenter + 331622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 331622]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06201_not_prime : ¬(recordGapCenter + 331746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 331746]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06202_not_prime : ¬(recordGapCenter + 331776).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 331776]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06203_not_prime : ¬(recordGapCenter + 331986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 331986]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06204_not_prime : ¬(recordGapCenter + 332106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 332106]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06205_not_prime : ¬(recordGapCenter + 332126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 332126]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06206_not_prime : ¬(recordGapCenter + 332162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 332162]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06207_not_prime : ¬(recordGapCenter + 332252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 332252]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

theorem fullRecordGapTerm06208_not_prime : ¬(recordGapCenter + 332286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 332286]
  · apply fullRecordGapRow00097_fermat
    simp [fullRecordGapRow00097_values]

end PrimeFactorUnimodality
