import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00113_values : List Nat :=
  [fullRecordGapCenterValue + 406898,
    fullRecordGapCenterValue + 406988,
    fullRecordGapCenterValue + 407058,
    fullRecordGapCenterValue + 407118,
    fullRecordGapCenterValue + 407138,
    fullRecordGapCenterValue + 407298,
    fullRecordGapCenterValue + 407318,
    fullRecordGapCenterValue + 407346,
    fullRecordGapCenterValue + 407432,
    fullRecordGapCenterValue + 407492,
    fullRecordGapCenterValue + 407516,
    fullRecordGapCenterValue + 407522,
    fullRecordGapCenterValue + 407802,
    fullRecordGapCenterValue + 407906,
    fullRecordGapCenterValue + 407912,
    fullRecordGapCenterValue + 407996,
    fullRecordGapCenterValue + 408026,
    fullRecordGapCenterValue + 408236,
    fullRecordGapCenterValue + 408308,
    fullRecordGapCenterValue + 408326,
    fullRecordGapCenterValue + 408522,
    fullRecordGapCenterValue + 408662,
    fullRecordGapCenterValue + 408678,
    fullRecordGapCenterValue + 408788,
    fullRecordGapCenterValue + 408846,
    fullRecordGapCenterValue + 409172,
    fullRecordGapCenterValue + 409208,
    fullRecordGapCenterValue + 409256,
    fullRecordGapCenterValue + 409278,
    fullRecordGapCenterValue + 409358,
    fullRecordGapCenterValue + 409466,
    fullRecordGapCenterValue + 409586,
    fullRecordGapCenterValue + 409748,
    fullRecordGapCenterValue + 409826,
    fullRecordGapCenterValue + 409866,
    fullRecordGapCenterValue + 409958,
    fullRecordGapCenterValue + 410126,
    fullRecordGapCenterValue + 410132,
    fullRecordGapCenterValue + 410138,
    fullRecordGapCenterValue + 410156,
    fullRecordGapCenterValue + 410162,
    fullRecordGapCenterValue + 410258,
    fullRecordGapCenterValue + 410372,
    fullRecordGapCenterValue + 410456,
    fullRecordGapCenterValue + 410622,
    fullRecordGapCenterValue + 410658,
    fullRecordGapCenterValue + 410792,
    fullRecordGapCenterValue + 410862,
    fullRecordGapCenterValue + 410898,
    fullRecordGapCenterValue + 410966,
    fullRecordGapCenterValue + 411038,
    fullRecordGapCenterValue + 411042,
    fullRecordGapCenterValue + 411258,
    fullRecordGapCenterValue + 411512,
    fullRecordGapCenterValue + 411518,
    fullRecordGapCenterValue + 411566,
    fullRecordGapCenterValue + 411582,
    fullRecordGapCenterValue + 411666,
    fullRecordGapCenterValue + 411848,
    fullRecordGapCenterValue + 411962,
    fullRecordGapCenterValue + 412136,
    fullRecordGapCenterValue + 412172,
    fullRecordGapCenterValue + 412196,
    fullRecordGapCenterValue + 412266]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00113_fermat : ∀ n ∈ fullRecordGapRow00113_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07169_not_prime : ¬(recordGapCenter + 406898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406898]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07170_not_prime : ¬(recordGapCenter + 406988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406988]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07171_not_prime : ¬(recordGapCenter + 407058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 407058]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07172_not_prime : ¬(recordGapCenter + 407118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 407118]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07173_not_prime : ¬(recordGapCenter + 407138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 407138]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07174_not_prime : ¬(recordGapCenter + 407298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 407298]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07175_not_prime : ¬(recordGapCenter + 407318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 407318]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07176_not_prime : ¬(recordGapCenter + 407346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 407346]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07177_not_prime : ¬(recordGapCenter + 407432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 407432]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07178_not_prime : ¬(recordGapCenter + 407492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 407492]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07179_not_prime : ¬(recordGapCenter + 407516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 407516]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07180_not_prime : ¬(recordGapCenter + 407522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 407522]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07181_not_prime : ¬(recordGapCenter + 407802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 407802]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07182_not_prime : ¬(recordGapCenter + 407906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 407906]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07183_not_prime : ¬(recordGapCenter + 407912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 407912]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07184_not_prime : ¬(recordGapCenter + 407996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 407996]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07185_not_prime : ¬(recordGapCenter + 408026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 408026]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07186_not_prime : ¬(recordGapCenter + 408236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 408236]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07187_not_prime : ¬(recordGapCenter + 408308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 408308]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07188_not_prime : ¬(recordGapCenter + 408326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 408326]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07189_not_prime : ¬(recordGapCenter + 408522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 408522]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07190_not_prime : ¬(recordGapCenter + 408662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 408662]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07191_not_prime : ¬(recordGapCenter + 408678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 408678]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07192_not_prime : ¬(recordGapCenter + 408788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 408788]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07193_not_prime : ¬(recordGapCenter + 408846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 408846]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07194_not_prime : ¬(recordGapCenter + 409172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 409172]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07195_not_prime : ¬(recordGapCenter + 409208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 409208]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07196_not_prime : ¬(recordGapCenter + 409256).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 409256]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07197_not_prime : ¬(recordGapCenter + 409278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 409278]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07198_not_prime : ¬(recordGapCenter + 409358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 409358]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07199_not_prime : ¬(recordGapCenter + 409466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 409466]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07200_not_prime : ¬(recordGapCenter + 409586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 409586]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07201_not_prime : ¬(recordGapCenter + 409748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 409748]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07202_not_prime : ¬(recordGapCenter + 409826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 409826]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07203_not_prime : ¬(recordGapCenter + 409866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 409866]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07204_not_prime : ¬(recordGapCenter + 409958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 409958]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07205_not_prime : ¬(recordGapCenter + 410126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 410126]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07206_not_prime : ¬(recordGapCenter + 410132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 410132]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07207_not_prime : ¬(recordGapCenter + 410138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 410138]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07208_not_prime : ¬(recordGapCenter + 410156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 410156]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07209_not_prime : ¬(recordGapCenter + 410162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 410162]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07210_not_prime : ¬(recordGapCenter + 410258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 410258]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07211_not_prime : ¬(recordGapCenter + 410372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 410372]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07212_not_prime : ¬(recordGapCenter + 410456).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 410456]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07213_not_prime : ¬(recordGapCenter + 410622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 410622]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07214_not_prime : ¬(recordGapCenter + 410658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 410658]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07215_not_prime : ¬(recordGapCenter + 410792).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 410792]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07216_not_prime : ¬(recordGapCenter + 410862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 410862]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07217_not_prime : ¬(recordGapCenter + 410898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 410898]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07218_not_prime : ¬(recordGapCenter + 410966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 410966]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07219_not_prime : ¬(recordGapCenter + 411038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 411038]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07220_not_prime : ¬(recordGapCenter + 411042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 411042]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07221_not_prime : ¬(recordGapCenter + 411258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 411258]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07222_not_prime : ¬(recordGapCenter + 411512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 411512]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07223_not_prime : ¬(recordGapCenter + 411518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 411518]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07224_not_prime : ¬(recordGapCenter + 411566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 411566]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07225_not_prime : ¬(recordGapCenter + 411582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 411582]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07226_not_prime : ¬(recordGapCenter + 411666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 411666]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07227_not_prime : ¬(recordGapCenter + 411848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 411848]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07228_not_prime : ¬(recordGapCenter + 411962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 411962]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07229_not_prime : ¬(recordGapCenter + 412136).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 412136]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07230_not_prime : ¬(recordGapCenter + 412172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 412172]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07231_not_prime : ¬(recordGapCenter + 412196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 412196]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

theorem fullRecordGapTerm07232_not_prime : ¬(recordGapCenter + 412266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 412266]
  · apply fullRecordGapRow00113_fermat
    simp [fullRecordGapRow00113_values]

end PrimeFactorUnimodality
