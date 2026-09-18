import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00129_values : List Nat :=
  [fullRecordGapCenterValue + 483222,
    fullRecordGapCenterValue + 483302,
    fullRecordGapCenterValue + 483326,
    fullRecordGapCenterValue + 483422,
    fullRecordGapCenterValue + 483596,
    fullRecordGapCenterValue + 483618,
    fullRecordGapCenterValue + 483668,
    fullRecordGapCenterValue + 483830,
    fullRecordGapCenterValue + 483840,
    fullRecordGapCenterValue + 483926,
    fullRecordGapCenterValue + 483942,
    fullRecordGapCenterValue + 484026,
    fullRecordGapCenterValue + 484076,
    fullRecordGapCenterValue + 484086,
    fullRecordGapCenterValue + 484166,
    fullRecordGapCenterValue + 484202,
    fullRecordGapCenterValue + 484628,
    fullRecordGapCenterValue + 484712,
    fullRecordGapCenterValue + 484982,
    fullRecordGapCenterValue + 484998,
    fullRecordGapCenterValue + 485018,
    fullRecordGapCenterValue + 485102,
    fullRecordGapCenterValue + 485178,
    fullRecordGapCenterValue + 485252,
    fullRecordGapCenterValue + 485270,
    fullRecordGapCenterValue + 485378,
    fullRecordGapCenterValue + 485390,
    fullRecordGapCenterValue + 485396,
    fullRecordGapCenterValue + 485468,
    fullRecordGapCenterValue + 485516,
    fullRecordGapCenterValue + 485546,
    fullRecordGapCenterValue + 485612,
    fullRecordGapCenterValue + 485846,
    fullRecordGapCenterValue + 485930,
    fullRecordGapCenterValue + 485942,
    fullRecordGapCenterValue + 485948,
    fullRecordGapCenterValue + 485972,
    fullRecordGapCenterValue + 485978,
    fullRecordGapCenterValue + 486000,
    fullRecordGapCenterValue + 486182,
    fullRecordGapCenterValue + 486188,
    fullRecordGapCenterValue + 486236,
    fullRecordGapCenterValue + 486258,
    fullRecordGapCenterValue + 486462,
    fullRecordGapCenterValue + 486488,
    fullRecordGapCenterValue + 486582,
    fullRecordGapCenterValue + 486602,
    fullRecordGapCenterValue + 486606,
    fullRecordGapCenterValue + 486686,
    fullRecordGapCenterValue + 486782,
    fullRecordGapCenterValue + 486788,
    fullRecordGapCenterValue + 486806,
    fullRecordGapCenterValue + 486872,
    fullRecordGapCenterValue + 486942,
    fullRecordGapCenterValue + 487148,
    fullRecordGapCenterValue + 487166,
    fullRecordGapCenterValue + 487218,
    fullRecordGapCenterValue + 487226,
    fullRecordGapCenterValue + 487310,
    fullRecordGapCenterValue + 487338,
    fullRecordGapCenterValue + 487398,
    fullRecordGapCenterValue + 487496,
    fullRecordGapCenterValue + 487688,
    fullRecordGapCenterValue + 487748]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00129_fermat : ∀ n ∈ fullRecordGapRow00129_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08193_not_prime : ¬(recordGapCenter + 483222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483222]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08194_not_prime : ¬(recordGapCenter + 483302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483302]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08195_not_prime : ¬(recordGapCenter + 483326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483326]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08196_not_prime : ¬(recordGapCenter + 483422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483422]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08197_not_prime : ¬(recordGapCenter + 483596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483596]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08198_not_prime : ¬(recordGapCenter + 483618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483618]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08199_not_prime : ¬(recordGapCenter + 483668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483668]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08200_not_prime : ¬(recordGapCenter + 483830).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483830]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08201_not_prime : ¬(recordGapCenter + 483840).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483840]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08202_not_prime : ¬(recordGapCenter + 483926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483926]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08203_not_prime : ¬(recordGapCenter + 483942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483942]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08204_not_prime : ¬(recordGapCenter + 484026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484026]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08205_not_prime : ¬(recordGapCenter + 484076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484076]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08206_not_prime : ¬(recordGapCenter + 484086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484086]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08207_not_prime : ¬(recordGapCenter + 484166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484166]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08208_not_prime : ¬(recordGapCenter + 484202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484202]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08209_not_prime : ¬(recordGapCenter + 484628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484628]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08210_not_prime : ¬(recordGapCenter + 484712).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484712]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08211_not_prime : ¬(recordGapCenter + 484982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484982]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08212_not_prime : ¬(recordGapCenter + 484998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484998]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08213_not_prime : ¬(recordGapCenter + 485018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485018]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08214_not_prime : ¬(recordGapCenter + 485102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485102]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08215_not_prime : ¬(recordGapCenter + 485178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485178]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08216_not_prime : ¬(recordGapCenter + 485252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485252]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08217_not_prime : ¬(recordGapCenter + 485270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485270]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08218_not_prime : ¬(recordGapCenter + 485378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485378]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08219_not_prime : ¬(recordGapCenter + 485390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485390]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08220_not_prime : ¬(recordGapCenter + 485396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485396]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08221_not_prime : ¬(recordGapCenter + 485468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485468]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08222_not_prime : ¬(recordGapCenter + 485516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485516]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08223_not_prime : ¬(recordGapCenter + 485546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485546]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08224_not_prime : ¬(recordGapCenter + 485612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485612]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08225_not_prime : ¬(recordGapCenter + 485846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485846]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08226_not_prime : ¬(recordGapCenter + 485930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485930]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08227_not_prime : ¬(recordGapCenter + 485942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485942]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08228_not_prime : ¬(recordGapCenter + 485948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485948]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08229_not_prime : ¬(recordGapCenter + 485972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485972]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08230_not_prime : ¬(recordGapCenter + 485978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485978]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08231_not_prime : ¬(recordGapCenter + 486000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486000]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08232_not_prime : ¬(recordGapCenter + 486182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486182]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08233_not_prime : ¬(recordGapCenter + 486188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486188]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08234_not_prime : ¬(recordGapCenter + 486236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486236]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08235_not_prime : ¬(recordGapCenter + 486258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486258]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08236_not_prime : ¬(recordGapCenter + 486462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486462]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08237_not_prime : ¬(recordGapCenter + 486488).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486488]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08238_not_prime : ¬(recordGapCenter + 486582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486582]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08239_not_prime : ¬(recordGapCenter + 486602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486602]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08240_not_prime : ¬(recordGapCenter + 486606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486606]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08241_not_prime : ¬(recordGapCenter + 486686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486686]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08242_not_prime : ¬(recordGapCenter + 486782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486782]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08243_not_prime : ¬(recordGapCenter + 486788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486788]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08244_not_prime : ¬(recordGapCenter + 486806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486806]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08245_not_prime : ¬(recordGapCenter + 486872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486872]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08246_not_prime : ¬(recordGapCenter + 486942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486942]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08247_not_prime : ¬(recordGapCenter + 487148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487148]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08248_not_prime : ¬(recordGapCenter + 487166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487166]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08249_not_prime : ¬(recordGapCenter + 487218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487218]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08250_not_prime : ¬(recordGapCenter + 487226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487226]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08251_not_prime : ¬(recordGapCenter + 487310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487310]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08252_not_prime : ¬(recordGapCenter + 487338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487338]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08253_not_prime : ¬(recordGapCenter + 487398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487398]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08254_not_prime : ¬(recordGapCenter + 487496).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487496]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08255_not_prime : ¬(recordGapCenter + 487688).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487688]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

theorem fullRecordGapTerm08256_not_prime : ¬(recordGapCenter + 487748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487748]
  · apply fullRecordGapRow00129_fermat
    simp [fullRecordGapRow00129_values]

end PrimeFactorUnimodality
