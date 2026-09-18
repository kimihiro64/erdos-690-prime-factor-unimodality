import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00020_values : List Nat :=
  [fullRecordGapCenterValue - 358222,
    fullRecordGapCenterValue - 358108,
    fullRecordGapCenterValue - 358042,
    fullRecordGapCenterValue - 357772,
    fullRecordGapCenterValue - 357762,
    fullRecordGapCenterValue - 357718,
    fullRecordGapCenterValue - 357402,
    fullRecordGapCenterValue - 357342,
    fullRecordGapCenterValue - 357268,
    fullRecordGapCenterValue - 357234,
    fullRecordGapCenterValue - 357208,
    fullRecordGapCenterValue - 357202,
    fullRecordGapCenterValue - 356982,
    fullRecordGapCenterValue - 356974,
    fullRecordGapCenterValue - 356962,
    fullRecordGapCenterValue - 356838,
    fullRecordGapCenterValue - 356802,
    fullRecordGapCenterValue - 356722,
    fullRecordGapCenterValue - 356718,
    fullRecordGapCenterValue - 356614,
    fullRecordGapCenterValue - 356502,
    fullRecordGapCenterValue - 356494,
    fullRecordGapCenterValue - 356400,
    fullRecordGapCenterValue - 356394,
    fullRecordGapCenterValue - 356374,
    fullRecordGapCenterValue - 356262,
    fullRecordGapCenterValue - 356248,
    fullRecordGapCenterValue - 356214,
    fullRecordGapCenterValue - 356164,
    fullRecordGapCenterValue - 356142,
    fullRecordGapCenterValue - 356002,
    fullRecordGapCenterValue - 355998,
    fullRecordGapCenterValue - 355864,
    fullRecordGapCenterValue - 355858,
    fullRecordGapCenterValue - 355582,
    fullRecordGapCenterValue - 355492,
    fullRecordGapCenterValue - 355444,
    fullRecordGapCenterValue - 355434,
    fullRecordGapCenterValue - 355294,
    fullRecordGapCenterValue - 355254,
    fullRecordGapCenterValue - 355252,
    fullRecordGapCenterValue - 355242,
    fullRecordGapCenterValue - 355228,
    fullRecordGapCenterValue - 355098,
    fullRecordGapCenterValue - 355078,
    fullRecordGapCenterValue - 354988,
    fullRecordGapCenterValue - 354808,
    fullRecordGapCenterValue - 354724,
    fullRecordGapCenterValue - 354652,
    fullRecordGapCenterValue - 354604,
    fullRecordGapCenterValue - 354538,
    fullRecordGapCenterValue - 354478,
    fullRecordGapCenterValue - 354378,
    fullRecordGapCenterValue - 354364,
    fullRecordGapCenterValue - 354294,
    fullRecordGapCenterValue - 354232,
    fullRecordGapCenterValue - 354202,
    fullRecordGapCenterValue - 354184,
    fullRecordGapCenterValue - 354174,
    fullRecordGapCenterValue - 354052,
    fullRecordGapCenterValue - 353902,
    fullRecordGapCenterValue - 353692,
    fullRecordGapCenterValue - 353638,
    fullRecordGapCenterValue - 353512]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00020_fermat : ∀ n ∈ fullRecordGapRow00020_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01217_not_prime : ¬(recordGapCenter - 358222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358222]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01218_not_prime : ¬(recordGapCenter - 358108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358108]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01219_not_prime : ¬(recordGapCenter - 358042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358042]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01220_not_prime : ¬(recordGapCenter - 357772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357772]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01221_not_prime : ¬(recordGapCenter - 357762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357762]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01222_not_prime : ¬(recordGapCenter - 357718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357718]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01223_not_prime : ¬(recordGapCenter - 357402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357402]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01224_not_prime : ¬(recordGapCenter - 357342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357342]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01225_not_prime : ¬(recordGapCenter - 357268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357268]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01226_not_prime : ¬(recordGapCenter - 357234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357234]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01227_not_prime : ¬(recordGapCenter - 357208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357208]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01228_not_prime : ¬(recordGapCenter - 357202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357202]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01229_not_prime : ¬(recordGapCenter - 356982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356982]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01230_not_prime : ¬(recordGapCenter - 356974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356974]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01231_not_prime : ¬(recordGapCenter - 356962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356962]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01232_not_prime : ¬(recordGapCenter - 356838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356838]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01233_not_prime : ¬(recordGapCenter - 356802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356802]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01234_not_prime : ¬(recordGapCenter - 356722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356722]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01235_not_prime : ¬(recordGapCenter - 356718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356718]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01236_not_prime : ¬(recordGapCenter - 356614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356614]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01237_not_prime : ¬(recordGapCenter - 356502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356502]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01238_not_prime : ¬(recordGapCenter - 356494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356494]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01239_not_prime : ¬(recordGapCenter - 356400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356400]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01240_not_prime : ¬(recordGapCenter - 356394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356394]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01241_not_prime : ¬(recordGapCenter - 356374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356374]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01242_not_prime : ¬(recordGapCenter - 356262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356262]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01243_not_prime : ¬(recordGapCenter - 356248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356248]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01244_not_prime : ¬(recordGapCenter - 356214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356214]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01245_not_prime : ¬(recordGapCenter - 356164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356164]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01246_not_prime : ¬(recordGapCenter - 356142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356142]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01247_not_prime : ¬(recordGapCenter - 356002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356002]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01248_not_prime : ¬(recordGapCenter - 355998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355998]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01249_not_prime : ¬(recordGapCenter - 355864).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355864]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01250_not_prime : ¬(recordGapCenter - 355858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355858]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01251_not_prime : ¬(recordGapCenter - 355582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355582]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01252_not_prime : ¬(recordGapCenter - 355492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355492]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01253_not_prime : ¬(recordGapCenter - 355444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355444]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01254_not_prime : ¬(recordGapCenter - 355434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355434]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01255_not_prime : ¬(recordGapCenter - 355294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355294]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01256_not_prime : ¬(recordGapCenter - 355254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355254]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01257_not_prime : ¬(recordGapCenter - 355252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355252]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01258_not_prime : ¬(recordGapCenter - 355242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355242]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01259_not_prime : ¬(recordGapCenter - 355228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355228]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01260_not_prime : ¬(recordGapCenter - 355098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355098]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01261_not_prime : ¬(recordGapCenter - 355078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355078]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01262_not_prime : ¬(recordGapCenter - 354988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354988]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01263_not_prime : ¬(recordGapCenter - 354808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354808]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01264_not_prime : ¬(recordGapCenter - 354724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354724]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01265_not_prime : ¬(recordGapCenter - 354652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354652]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01266_not_prime : ¬(recordGapCenter - 354604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354604]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01267_not_prime : ¬(recordGapCenter - 354538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354538]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01268_not_prime : ¬(recordGapCenter - 354478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354478]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01269_not_prime : ¬(recordGapCenter - 354378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354378]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01270_not_prime : ¬(recordGapCenter - 354364).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354364]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01271_not_prime : ¬(recordGapCenter - 354294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354294]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01272_not_prime : ¬(recordGapCenter - 354232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354232]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01273_not_prime : ¬(recordGapCenter - 354202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354202]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01274_not_prime : ¬(recordGapCenter - 354184).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354184]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01275_not_prime : ¬(recordGapCenter - 354174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354174]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01276_not_prime : ¬(recordGapCenter - 354052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354052]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01277_not_prime : ¬(recordGapCenter - 353902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353902]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01278_not_prime : ¬(recordGapCenter - 353692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353692]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01279_not_prime : ¬(recordGapCenter - 353638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353638]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

theorem fullRecordGapTerm01280_not_prime : ¬(recordGapCenter - 353512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353512]
  · apply fullRecordGapRow00020_fermat
    simp [fullRecordGapRow00020_values]

end PrimeFactorUnimodality
