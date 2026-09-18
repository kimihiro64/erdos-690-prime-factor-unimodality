import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00111_values : List Nat :=
  [fullRecordGapCenterValue + 396386,
    fullRecordGapCenterValue + 396426,
    fullRecordGapCenterValue + 396498,
    fullRecordGapCenterValue + 396692,
    fullRecordGapCenterValue + 396782,
    fullRecordGapCenterValue + 397058,
    fullRecordGapCenterValue + 397226,
    fullRecordGapCenterValue + 397346,
    fullRecordGapCenterValue + 397388,
    fullRecordGapCenterValue + 397622,
    fullRecordGapCenterValue + 397682,
    fullRecordGapCenterValue + 397688,
    fullRecordGapCenterValue + 397806,
    fullRecordGapCenterValue + 398078,
    fullRecordGapCenterValue + 398162,
    fullRecordGapCenterValue + 398252,
    fullRecordGapCenterValue + 398408,
    fullRecordGapCenterValue + 398756,
    fullRecordGapCenterValue + 398778,
    fullRecordGapCenterValue + 398798,
    fullRecordGapCenterValue + 398802,
    fullRecordGapCenterValue + 398822,
    fullRecordGapCenterValue + 398828,
    fullRecordGapCenterValue + 398858,
    fullRecordGapCenterValue + 398946,
    fullRecordGapCenterValue + 399002,
    fullRecordGapCenterValue + 399236,
    fullRecordGapCenterValue + 399242,
    fullRecordGapCenterValue + 399246,
    fullRecordGapCenterValue + 399332,
    fullRecordGapCenterValue + 399368,
    fullRecordGapCenterValue + 399458,
    fullRecordGapCenterValue + 399506,
    fullRecordGapCenterValue + 399512,
    fullRecordGapCenterValue + 399558,
    fullRecordGapCenterValue + 399638,
    fullRecordGapCenterValue + 399662,
    fullRecordGapCenterValue + 399702,
    fullRecordGapCenterValue + 399716,
    fullRecordGapCenterValue + 399746,
    fullRecordGapCenterValue + 399998,
    fullRecordGapCenterValue + 400046,
    fullRecordGapCenterValue + 400058,
    fullRecordGapCenterValue + 400082,
    fullRecordGapCenterValue + 400206,
    fullRecordGapCenterValue + 400382,
    fullRecordGapCenterValue + 400586,
    fullRecordGapCenterValue + 400676,
    fullRecordGapCenterValue + 400746,
    fullRecordGapCenterValue + 400766,
    fullRecordGapCenterValue + 400802,
    fullRecordGapCenterValue + 400886,
    fullRecordGapCenterValue + 400922,
    fullRecordGapCenterValue + 401252,
    fullRecordGapCenterValue + 401378,
    fullRecordGapCenterValue + 401426,
    fullRecordGapCenterValue + 401462,
    fullRecordGapCenterValue + 401516,
    fullRecordGapCenterValue + 401538,
    fullRecordGapCenterValue + 401586,
    fullRecordGapCenterValue + 401612,
    fullRecordGapCenterValue + 401762,
    fullRecordGapCenterValue + 401768,
    fullRecordGapCenterValue + 401798]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00111_fermat : ∀ n ∈ fullRecordGapRow00111_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07041_not_prime : ¬(recordGapCenter + 396386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396386]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07042_not_prime : ¬(recordGapCenter + 396426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396426]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07043_not_prime : ¬(recordGapCenter + 396498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396498]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07044_not_prime : ¬(recordGapCenter + 396692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396692]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07045_not_prime : ¬(recordGapCenter + 396782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396782]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07046_not_prime : ¬(recordGapCenter + 397058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397058]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07047_not_prime : ¬(recordGapCenter + 397226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397226]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07048_not_prime : ¬(recordGapCenter + 397346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397346]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07049_not_prime : ¬(recordGapCenter + 397388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397388]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07050_not_prime : ¬(recordGapCenter + 397622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397622]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07051_not_prime : ¬(recordGapCenter + 397682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397682]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07052_not_prime : ¬(recordGapCenter + 397688).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397688]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07053_not_prime : ¬(recordGapCenter + 397806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397806]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07054_not_prime : ¬(recordGapCenter + 398078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398078]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07055_not_prime : ¬(recordGapCenter + 398162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398162]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07056_not_prime : ¬(recordGapCenter + 398252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398252]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07057_not_prime : ¬(recordGapCenter + 398408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398408]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07058_not_prime : ¬(recordGapCenter + 398756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398756]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07059_not_prime : ¬(recordGapCenter + 398778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398778]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07060_not_prime : ¬(recordGapCenter + 398798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398798]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07061_not_prime : ¬(recordGapCenter + 398802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398802]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07062_not_prime : ¬(recordGapCenter + 398822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398822]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07063_not_prime : ¬(recordGapCenter + 398828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398828]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07064_not_prime : ¬(recordGapCenter + 398858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398858]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07065_not_prime : ¬(recordGapCenter + 398946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398946]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07066_not_prime : ¬(recordGapCenter + 399002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399002]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07067_not_prime : ¬(recordGapCenter + 399236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399236]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07068_not_prime : ¬(recordGapCenter + 399242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399242]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07069_not_prime : ¬(recordGapCenter + 399246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399246]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07070_not_prime : ¬(recordGapCenter + 399332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399332]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07071_not_prime : ¬(recordGapCenter + 399368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399368]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07072_not_prime : ¬(recordGapCenter + 399458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399458]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07073_not_prime : ¬(recordGapCenter + 399506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399506]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07074_not_prime : ¬(recordGapCenter + 399512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399512]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07075_not_prime : ¬(recordGapCenter + 399558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399558]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07076_not_prime : ¬(recordGapCenter + 399638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399638]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07077_not_prime : ¬(recordGapCenter + 399662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399662]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07078_not_prime : ¬(recordGapCenter + 399702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399702]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07079_not_prime : ¬(recordGapCenter + 399716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399716]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07080_not_prime : ¬(recordGapCenter + 399746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399746]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07081_not_prime : ¬(recordGapCenter + 399998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399998]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07082_not_prime : ¬(recordGapCenter + 400046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400046]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07083_not_prime : ¬(recordGapCenter + 400058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400058]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07084_not_prime : ¬(recordGapCenter + 400082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400082]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07085_not_prime : ¬(recordGapCenter + 400206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400206]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07086_not_prime : ¬(recordGapCenter + 400382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400382]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07087_not_prime : ¬(recordGapCenter + 400586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400586]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07088_not_prime : ¬(recordGapCenter + 400676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400676]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07089_not_prime : ¬(recordGapCenter + 400746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400746]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07090_not_prime : ¬(recordGapCenter + 400766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400766]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07091_not_prime : ¬(recordGapCenter + 400802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400802]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07092_not_prime : ¬(recordGapCenter + 400886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400886]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07093_not_prime : ¬(recordGapCenter + 400922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400922]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07094_not_prime : ¬(recordGapCenter + 401252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401252]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07095_not_prime : ¬(recordGapCenter + 401378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401378]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07096_not_prime : ¬(recordGapCenter + 401426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401426]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07097_not_prime : ¬(recordGapCenter + 401462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401462]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07098_not_prime : ¬(recordGapCenter + 401516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401516]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07099_not_prime : ¬(recordGapCenter + 401538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401538]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07100_not_prime : ¬(recordGapCenter + 401586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401586]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07101_not_prime : ¬(recordGapCenter + 401612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401612]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07102_not_prime : ¬(recordGapCenter + 401762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401762]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07103_not_prime : ¬(recordGapCenter + 401768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401768]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

theorem fullRecordGapTerm07104_not_prime : ¬(recordGapCenter + 401798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401798]
  · apply fullRecordGapRow00111_fermat
    simp [fullRecordGapRow00111_values]

end PrimeFactorUnimodality
