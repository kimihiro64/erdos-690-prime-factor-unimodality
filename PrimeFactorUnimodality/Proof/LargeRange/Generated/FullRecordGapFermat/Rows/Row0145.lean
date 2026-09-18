import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00145_values : List Nat :=
  [fullRecordGapCenterValue + 552018,
    fullRecordGapCenterValue + 552098,
    fullRecordGapCenterValue + 552158,
    fullRecordGapCenterValue + 552170,
    fullRecordGapCenterValue + 552182,
    fullRecordGapCenterValue + 552212,
    fullRecordGapCenterValue + 552252,
    fullRecordGapCenterValue + 552302,
    fullRecordGapCenterValue + 552428,
    fullRecordGapCenterValue + 552452,
    fullRecordGapCenterValue + 552458,
    fullRecordGapCenterValue + 552498,
    fullRecordGapCenterValue + 552536,
    fullRecordGapCenterValue + 552612,
    fullRecordGapCenterValue + 552638,
    fullRecordGapCenterValue + 552686,
    fullRecordGapCenterValue + 552716,
    fullRecordGapCenterValue + 552918,
    fullRecordGapCenterValue + 553092,
    fullRecordGapCenterValue + 553106,
    fullRecordGapCenterValue + 553130,
    fullRecordGapCenterValue + 553178,
    fullRecordGapCenterValue + 553292,
    fullRecordGapCenterValue + 553310,
    fullRecordGapCenterValue + 553458,
    fullRecordGapCenterValue + 553526,
    fullRecordGapCenterValue + 553556,
    fullRecordGapCenterValue + 553628,
    fullRecordGapCenterValue + 553646,
    fullRecordGapCenterValue + 553766,
    fullRecordGapCenterValue + 553782,
    fullRecordGapCenterValue + 553836,
    fullRecordGapCenterValue + 553998,
    fullRecordGapCenterValue + 554072,
    fullRecordGapCenterValue + 554178,
    fullRecordGapCenterValue + 554262,
    fullRecordGapCenterValue + 554276,
    fullRecordGapCenterValue + 554298,
    fullRecordGapCenterValue + 554366,
    fullRecordGapCenterValue + 554388,
    fullRecordGapCenterValue + 554390,
    fullRecordGapCenterValue + 554426,
    fullRecordGapCenterValue + 554468,
    fullRecordGapCenterValue + 554516,
    fullRecordGapCenterValue + 554522,
    fullRecordGapCenterValue + 554690,
    fullRecordGapCenterValue + 554696,
    fullRecordGapCenterValue + 554766,
    fullRecordGapCenterValue + 554802,
    fullRecordGapCenterValue + 554870,
    fullRecordGapCenterValue + 555018,
    fullRecordGapCenterValue + 555158,
    fullRecordGapCenterValue + 555278,
    fullRecordGapCenterValue + 555348,
    fullRecordGapCenterValue + 555402,
    fullRecordGapCenterValue + 555416,
    fullRecordGapCenterValue + 555486,
    fullRecordGapCenterValue + 555626,
    fullRecordGapCenterValue + 555660,
    fullRecordGapCenterValue + 555762,
    fullRecordGapCenterValue + 555986,
    fullRecordGapCenterValue + 555992,
    fullRecordGapCenterValue + 556082,
    fullRecordGapCenterValue + 556158]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00145_fermat : ∀ n ∈ fullRecordGapRow00145_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09217_not_prime : ¬(recordGapCenter + 552018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552018]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09218_not_prime : ¬(recordGapCenter + 552098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552098]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09219_not_prime : ¬(recordGapCenter + 552158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552158]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09220_not_prime : ¬(recordGapCenter + 552170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552170]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09221_not_prime : ¬(recordGapCenter + 552182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552182]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09222_not_prime : ¬(recordGapCenter + 552212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552212]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09223_not_prime : ¬(recordGapCenter + 552252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552252]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09224_not_prime : ¬(recordGapCenter + 552302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552302]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09225_not_prime : ¬(recordGapCenter + 552428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552428]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09226_not_prime : ¬(recordGapCenter + 552452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552452]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09227_not_prime : ¬(recordGapCenter + 552458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552458]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09228_not_prime : ¬(recordGapCenter + 552498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552498]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09229_not_prime : ¬(recordGapCenter + 552536).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552536]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09230_not_prime : ¬(recordGapCenter + 552612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552612]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09231_not_prime : ¬(recordGapCenter + 552638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552638]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09232_not_prime : ¬(recordGapCenter + 552686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552686]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09233_not_prime : ¬(recordGapCenter + 552716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552716]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09234_not_prime : ¬(recordGapCenter + 552918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 552918]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09235_not_prime : ¬(recordGapCenter + 553092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553092]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09236_not_prime : ¬(recordGapCenter + 553106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553106]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09237_not_prime : ¬(recordGapCenter + 553130).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553130]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09238_not_prime : ¬(recordGapCenter + 553178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553178]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09239_not_prime : ¬(recordGapCenter + 553292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553292]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09240_not_prime : ¬(recordGapCenter + 553310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553310]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09241_not_prime : ¬(recordGapCenter + 553458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553458]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09242_not_prime : ¬(recordGapCenter + 553526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553526]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09243_not_prime : ¬(recordGapCenter + 553556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553556]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09244_not_prime : ¬(recordGapCenter + 553628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553628]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09245_not_prime : ¬(recordGapCenter + 553646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553646]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09246_not_prime : ¬(recordGapCenter + 553766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553766]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09247_not_prime : ¬(recordGapCenter + 553782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553782]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09248_not_prime : ¬(recordGapCenter + 553836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553836]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09249_not_prime : ¬(recordGapCenter + 553998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 553998]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09250_not_prime : ¬(recordGapCenter + 554072).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554072]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09251_not_prime : ¬(recordGapCenter + 554178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554178]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09252_not_prime : ¬(recordGapCenter + 554262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554262]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09253_not_prime : ¬(recordGapCenter + 554276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554276]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09254_not_prime : ¬(recordGapCenter + 554298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554298]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09255_not_prime : ¬(recordGapCenter + 554366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554366]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09256_not_prime : ¬(recordGapCenter + 554388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554388]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09257_not_prime : ¬(recordGapCenter + 554390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554390]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09258_not_prime : ¬(recordGapCenter + 554426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554426]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09259_not_prime : ¬(recordGapCenter + 554468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554468]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09260_not_prime : ¬(recordGapCenter + 554516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554516]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09261_not_prime : ¬(recordGapCenter + 554522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554522]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09262_not_prime : ¬(recordGapCenter + 554690).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554690]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09263_not_prime : ¬(recordGapCenter + 554696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554696]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09264_not_prime : ¬(recordGapCenter + 554766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554766]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09265_not_prime : ¬(recordGapCenter + 554802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554802]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09266_not_prime : ¬(recordGapCenter + 554870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 554870]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09267_not_prime : ¬(recordGapCenter + 555018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 555018]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09268_not_prime : ¬(recordGapCenter + 555158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 555158]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09269_not_prime : ¬(recordGapCenter + 555278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 555278]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09270_not_prime : ¬(recordGapCenter + 555348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 555348]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09271_not_prime : ¬(recordGapCenter + 555402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 555402]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09272_not_prime : ¬(recordGapCenter + 555416).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 555416]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09273_not_prime : ¬(recordGapCenter + 555486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 555486]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09274_not_prime : ¬(recordGapCenter + 555626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 555626]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09275_not_prime : ¬(recordGapCenter + 555660).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 555660]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09276_not_prime : ¬(recordGapCenter + 555762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 555762]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09277_not_prime : ¬(recordGapCenter + 555986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 555986]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09278_not_prime : ¬(recordGapCenter + 555992).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 555992]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09279_not_prime : ¬(recordGapCenter + 556082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556082]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

theorem fullRecordGapTerm09280_not_prime : ¬(recordGapCenter + 556158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556158]
  · apply fullRecordGapRow00145_fermat
    simp [fullRecordGapRow00145_values]

end PrimeFactorUnimodality
