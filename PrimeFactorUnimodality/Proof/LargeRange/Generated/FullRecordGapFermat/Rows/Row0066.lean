import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00066_values : List Nat :=
  [fullRecordGapCenterValue + 101846,
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
    fullRecordGapCenterValue + 110798]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00066_fermat : ∀ n ∈ fullRecordGapRow00066_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04161_not_prime : ¬(recordGapCenter + 101846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 101846]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04162_not_prime : ¬(recordGapCenter + 102482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 102482]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04163_not_prime : ¬(recordGapCenter + 102686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 102686]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04164_not_prime : ¬(recordGapCenter + 102842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 102842]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04165_not_prime : ¬(recordGapCenter + 102900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 102900]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04166_not_prime : ¬(recordGapCenter + 103226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 103226]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04167_not_prime : ¬(recordGapCenter + 103346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 103346]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04168_not_prime : ¬(recordGapCenter + 103538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 103538]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04169_not_prime : ¬(recordGapCenter + 103826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 103826]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04170_not_prime : ¬(recordGapCenter + 103950).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 103950]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04171_not_prime : ¬(recordGapCenter + 103982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 103982]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04172_not_prime : ¬(recordGapCenter + 104018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 104018]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04173_not_prime : ¬(recordGapCenter + 104042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 104042]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04174_not_prime : ¬(recordGapCenter + 104102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 104102]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04175_not_prime : ¬(recordGapCenter + 104402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 104402]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04176_not_prime : ¬(recordGapCenter + 104498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 104498]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04177_not_prime : ¬(recordGapCenter + 104906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 104906]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04178_not_prime : ¬(recordGapCenter + 105000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105000]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04179_not_prime : ¬(recordGapCenter + 105086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105086]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04180_not_prime : ¬(recordGapCenter + 105158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105158]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04181_not_prime : ¬(recordGapCenter + 105218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105218]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04182_not_prime : ¬(recordGapCenter + 105600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105600]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04183_not_prime : ¬(recordGapCenter + 105626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105626]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04184_not_prime : ¬(recordGapCenter + 105722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105722]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04185_not_prime : ¬(recordGapCenter + 105758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105758]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04186_not_prime : ¬(recordGapCenter + 105840).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 105840]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04187_not_prime : ¬(recordGapCenter + 106178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 106178]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04188_not_prime : ¬(recordGapCenter + 106562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 106562]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04189_not_prime : ¬(recordGapCenter + 106598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 106598]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04190_not_prime : ¬(recordGapCenter + 106802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 106802]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04191_not_prime : ¬(recordGapCenter + 106838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 106838]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04192_not_prime : ¬(recordGapCenter + 106920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 106920]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04193_not_prime : ¬(recordGapCenter + 107006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 107006]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04194_not_prime : ¬(recordGapCenter + 107102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 107102]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04195_not_prime : ¬(recordGapCenter + 107138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 107138]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04196_not_prime : ¬(recordGapCenter + 107258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 107258]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04197_not_prime : ¬(recordGapCenter + 107520).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 107520]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04198_not_prime : ¬(recordGapCenter + 107798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 107798]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04199_not_prime : ¬(recordGapCenter + 107846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 107846]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04200_not_prime : ¬(recordGapCenter + 108000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108000]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04201_not_prime : ¬(recordGapCenter + 108182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108182]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04202_not_prime : ¬(recordGapCenter + 108242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108242]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04203_not_prime : ¬(recordGapCenter + 108266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108266]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04204_not_prime : ¬(recordGapCenter + 108278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108278]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04205_not_prime : ¬(recordGapCenter + 108326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108326]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04206_not_prime : ¬(recordGapCenter + 108362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108362]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04207_not_prime : ¬(recordGapCenter + 108638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108638]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04208_not_prime : ¬(recordGapCenter + 108662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108662]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04209_not_prime : ¬(recordGapCenter + 108722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108722]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04210_not_prime : ¬(recordGapCenter + 108938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108938]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04211_not_prime : ¬(recordGapCenter + 108986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 108986]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04212_not_prime : ¬(recordGapCenter + 109082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109082]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04213_not_prime : ¬(recordGapCenter + 109118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109118]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04214_not_prime : ¬(recordGapCenter + 109166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109166]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04215_not_prime : ¬(recordGapCenter + 109202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109202]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04216_not_prime : ¬(recordGapCenter + 109350).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109350]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04217_not_prime : ¬(recordGapCenter + 109658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109658]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04218_not_prime : ¬(recordGapCenter + 109898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109898]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04219_not_prime : ¬(recordGapCenter + 109946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 109946]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04220_not_prime : ¬(recordGapCenter + 110426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 110426]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04221_not_prime : ¬(recordGapCenter + 110486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 110486]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04222_not_prime : ¬(recordGapCenter + 110498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 110498]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04223_not_prime : ¬(recordGapCenter + 110666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 110666]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

theorem fullRecordGapTerm04224_not_prime : ¬(recordGapCenter + 110798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 110798]
  · apply fullRecordGapRow00066_fermat
    simp [fullRecordGapRow00066_values]

end PrimeFactorUnimodality
