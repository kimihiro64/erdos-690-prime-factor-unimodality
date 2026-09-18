import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00019_values : List Nat :=
  [fullRecordGapCenterValue - 363894,
    fullRecordGapCenterValue - 363838,
    fullRecordGapCenterValue - 363778,
    fullRecordGapCenterValue - 363604,
    fullRecordGapCenterValue - 363502,
    fullRecordGapCenterValue - 363388,
    fullRecordGapCenterValue - 363304,
    fullRecordGapCenterValue - 363172,
    fullRecordGapCenterValue - 363162,
    fullRecordGapCenterValue - 362998,
    fullRecordGapCenterValue - 362794,
    fullRecordGapCenterValue - 362728,
    fullRecordGapCenterValue - 362694,
    fullRecordGapCenterValue - 362632,
    fullRecordGapCenterValue - 362602,
    fullRecordGapCenterValue - 362562,
    fullRecordGapCenterValue - 362554,
    fullRecordGapCenterValue - 362478,
    fullRecordGapCenterValue - 362422,
    fullRecordGapCenterValue - 362382,
    fullRecordGapCenterValue - 362248,
    fullRecordGapCenterValue - 362238,
    fullRecordGapCenterValue - 362022,
    fullRecordGapCenterValue - 361918,
    fullRecordGapCenterValue - 361902,
    fullRecordGapCenterValue - 361554,
    fullRecordGapCenterValue - 361542,
    fullRecordGapCenterValue - 361462,
    fullRecordGapCenterValue - 361302,
    fullRecordGapCenterValue - 361234,
    fullRecordGapCenterValue - 361084,
    fullRecordGapCenterValue - 360988,
    fullRecordGapCenterValue - 360762,
    fullRecordGapCenterValue - 360748,
    fullRecordGapCenterValue - 360652,
    fullRecordGapCenterValue - 360642,
    fullRecordGapCenterValue - 360534,
    fullRecordGapCenterValue - 360448,
    fullRecordGapCenterValue - 360442,
    fullRecordGapCenterValue - 360292,
    fullRecordGapCenterValue - 360268,
    fullRecordGapCenterValue - 360222,
    fullRecordGapCenterValue - 360154,
    fullRecordGapCenterValue - 360124,
    fullRecordGapCenterValue - 359998,
    fullRecordGapCenterValue - 359938,
    fullRecordGapCenterValue - 359914,
    fullRecordGapCenterValue - 359908,
    fullRecordGapCenterValue - 359692,
    fullRecordGapCenterValue - 359614,
    fullRecordGapCenterValue - 359182,
    fullRecordGapCenterValue - 359068,
    fullRecordGapCenterValue - 358942,
    fullRecordGapCenterValue - 358854,
    fullRecordGapCenterValue - 358762,
    fullRecordGapCenterValue - 358738,
    fullRecordGapCenterValue - 358684,
    fullRecordGapCenterValue - 358642,
    fullRecordGapCenterValue - 358522,
    fullRecordGapCenterValue - 358482,
    fullRecordGapCenterValue - 358458,
    fullRecordGapCenterValue - 358444,
    fullRecordGapCenterValue - 358374,
    fullRecordGapCenterValue - 358312]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00019_fermat : ∀ n ∈ fullRecordGapRow00019_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01153_not_prime : ¬(recordGapCenter - 363894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363894]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01154_not_prime : ¬(recordGapCenter - 363838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363838]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01155_not_prime : ¬(recordGapCenter - 363778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363778]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01156_not_prime : ¬(recordGapCenter - 363604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363604]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01157_not_prime : ¬(recordGapCenter - 363502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363502]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01158_not_prime : ¬(recordGapCenter - 363388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363388]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01159_not_prime : ¬(recordGapCenter - 363304).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363304]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01160_not_prime : ¬(recordGapCenter - 363172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363172]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01161_not_prime : ¬(recordGapCenter - 363162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363162]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01162_not_prime : ¬(recordGapCenter - 362998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362998]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01163_not_prime : ¬(recordGapCenter - 362794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362794]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01164_not_prime : ¬(recordGapCenter - 362728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362728]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01165_not_prime : ¬(recordGapCenter - 362694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362694]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01166_not_prime : ¬(recordGapCenter - 362632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362632]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01167_not_prime : ¬(recordGapCenter - 362602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362602]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01168_not_prime : ¬(recordGapCenter - 362562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362562]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01169_not_prime : ¬(recordGapCenter - 362554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362554]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01170_not_prime : ¬(recordGapCenter - 362478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362478]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01171_not_prime : ¬(recordGapCenter - 362422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362422]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01172_not_prime : ¬(recordGapCenter - 362382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362382]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01173_not_prime : ¬(recordGapCenter - 362248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362248]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01174_not_prime : ¬(recordGapCenter - 362238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362238]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01175_not_prime : ¬(recordGapCenter - 362022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362022]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01176_not_prime : ¬(recordGapCenter - 361918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361918]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01177_not_prime : ¬(recordGapCenter - 361902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361902]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01178_not_prime : ¬(recordGapCenter - 361554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361554]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01179_not_prime : ¬(recordGapCenter - 361542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361542]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01180_not_prime : ¬(recordGapCenter - 361462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361462]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01181_not_prime : ¬(recordGapCenter - 361302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361302]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01182_not_prime : ¬(recordGapCenter - 361234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361234]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01183_not_prime : ¬(recordGapCenter - 361084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361084]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01184_not_prime : ¬(recordGapCenter - 360988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360988]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01185_not_prime : ¬(recordGapCenter - 360762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360762]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01186_not_prime : ¬(recordGapCenter - 360748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360748]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01187_not_prime : ¬(recordGapCenter - 360652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360652]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01188_not_prime : ¬(recordGapCenter - 360642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360642]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01189_not_prime : ¬(recordGapCenter - 360534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360534]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01190_not_prime : ¬(recordGapCenter - 360448).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360448]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01191_not_prime : ¬(recordGapCenter - 360442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360442]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01192_not_prime : ¬(recordGapCenter - 360292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360292]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01193_not_prime : ¬(recordGapCenter - 360268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360268]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01194_not_prime : ¬(recordGapCenter - 360222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360222]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01195_not_prime : ¬(recordGapCenter - 360154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360154]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01196_not_prime : ¬(recordGapCenter - 360124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360124]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01197_not_prime : ¬(recordGapCenter - 359998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359998]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01198_not_prime : ¬(recordGapCenter - 359938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359938]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01199_not_prime : ¬(recordGapCenter - 359914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359914]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01200_not_prime : ¬(recordGapCenter - 359908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359908]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01201_not_prime : ¬(recordGapCenter - 359692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359692]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01202_not_prime : ¬(recordGapCenter - 359614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359614]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01203_not_prime : ¬(recordGapCenter - 359182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359182]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01204_not_prime : ¬(recordGapCenter - 359068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359068]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01205_not_prime : ¬(recordGapCenter - 358942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358942]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01206_not_prime : ¬(recordGapCenter - 358854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358854]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01207_not_prime : ¬(recordGapCenter - 358762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358762]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01208_not_prime : ¬(recordGapCenter - 358738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358738]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01209_not_prime : ¬(recordGapCenter - 358684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358684]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01210_not_prime : ¬(recordGapCenter - 358642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358642]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01211_not_prime : ¬(recordGapCenter - 358522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358522]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01212_not_prime : ¬(recordGapCenter - 358482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358482]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01213_not_prime : ¬(recordGapCenter - 358458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358458]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01214_not_prime : ¬(recordGapCenter - 358444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358444]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01215_not_prime : ¬(recordGapCenter - 358374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358374]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

theorem fullRecordGapTerm01216_not_prime : ¬(recordGapCenter - 358312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358312]
  · apply fullRecordGapRow00019_fermat
    simp [fullRecordGapRow00019_values]

end PrimeFactorUnimodality
