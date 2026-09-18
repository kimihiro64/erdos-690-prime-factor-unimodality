import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00035_values : List Nat :=
  [fullRecordGapCenterValue - 277200,
    fullRecordGapCenterValue - 277162,
    fullRecordGapCenterValue - 277122,
    fullRecordGapCenterValue - 276988,
    fullRecordGapCenterValue - 276814,
    fullRecordGapCenterValue - 276618,
    fullRecordGapCenterValue - 276604,
    fullRecordGapCenterValue - 276594,
    fullRecordGapCenterValue - 276502,
    fullRecordGapCenterValue - 276358,
    fullRecordGapCenterValue - 276294,
    fullRecordGapCenterValue - 276268,
    fullRecordGapCenterValue - 276162,
    fullRecordGapCenterValue - 276154,
    fullRecordGapCenterValue - 276124,
    fullRecordGapCenterValue - 275788,
    fullRecordGapCenterValue - 275734,
    fullRecordGapCenterValue - 275718,
    fullRecordGapCenterValue - 275694,
    fullRecordGapCenterValue - 275562,
    fullRecordGapCenterValue - 275524,
    fullRecordGapCenterValue - 275214,
    fullRecordGapCenterValue - 275194,
    fullRecordGapCenterValue - 275118,
    fullRecordGapCenterValue - 274972,
    fullRecordGapCenterValue - 274902,
    fullRecordGapCenterValue - 274738,
    fullRecordGapCenterValue - 274732,
    fullRecordGapCenterValue - 274678,
    fullRecordGapCenterValue - 274578,
    fullRecordGapCenterValue - 274558,
    fullRecordGapCenterValue - 274402,
    fullRecordGapCenterValue - 274242,
    fullRecordGapCenterValue - 274084,
    fullRecordGapCenterValue - 273982,
    fullRecordGapCenterValue - 273748,
    fullRecordGapCenterValue - 273682,
    fullRecordGapCenterValue - 273622,
    fullRecordGapCenterValue - 273538,
    fullRecordGapCenterValue - 273534,
    fullRecordGapCenterValue - 273502,
    fullRecordGapCenterValue - 273454,
    fullRecordGapCenterValue - 273318,
    fullRecordGapCenterValue - 273214,
    fullRecordGapCenterValue - 273198,
    fullRecordGapCenterValue - 273018,
    fullRecordGapCenterValue - 272962,
    fullRecordGapCenterValue - 272908,
    fullRecordGapCenterValue - 272638,
    fullRecordGapCenterValue - 272284,
    fullRecordGapCenterValue - 272262,
    fullRecordGapCenterValue - 272212,
    fullRecordGapCenterValue - 272092,
    fullRecordGapCenterValue - 271974,
    fullRecordGapCenterValue - 271954,
    fullRecordGapCenterValue - 271948,
    fullRecordGapCenterValue - 271914,
    fullRecordGapCenterValue - 271842,
    fullRecordGapCenterValue - 271798,
    fullRecordGapCenterValue - 271758,
    fullRecordGapCenterValue - 271732,
    fullRecordGapCenterValue - 271578,
    fullRecordGapCenterValue - 271564,
    fullRecordGapCenterValue - 271554]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00035_fermat : ∀ n ∈ fullRecordGapRow00035_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02177_not_prime : ¬(recordGapCenter - 277200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277200]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02178_not_prime : ¬(recordGapCenter - 277162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277162]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02179_not_prime : ¬(recordGapCenter - 277122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 277122]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02180_not_prime : ¬(recordGapCenter - 276988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276988]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02181_not_prime : ¬(recordGapCenter - 276814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276814]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02182_not_prime : ¬(recordGapCenter - 276618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276618]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02183_not_prime : ¬(recordGapCenter - 276604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276604]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02184_not_prime : ¬(recordGapCenter - 276594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276594]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02185_not_prime : ¬(recordGapCenter - 276502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276502]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02186_not_prime : ¬(recordGapCenter - 276358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276358]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02187_not_prime : ¬(recordGapCenter - 276294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276294]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02188_not_prime : ¬(recordGapCenter - 276268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276268]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02189_not_prime : ¬(recordGapCenter - 276162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276162]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02190_not_prime : ¬(recordGapCenter - 276154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276154]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02191_not_prime : ¬(recordGapCenter - 276124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 276124]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02192_not_prime : ¬(recordGapCenter - 275788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275788]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02193_not_prime : ¬(recordGapCenter - 275734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275734]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02194_not_prime : ¬(recordGapCenter - 275718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275718]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02195_not_prime : ¬(recordGapCenter - 275694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275694]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02196_not_prime : ¬(recordGapCenter - 275562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275562]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02197_not_prime : ¬(recordGapCenter - 275524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275524]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02198_not_prime : ¬(recordGapCenter - 275214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275214]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02199_not_prime : ¬(recordGapCenter - 275194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275194]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02200_not_prime : ¬(recordGapCenter - 275118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 275118]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02201_not_prime : ¬(recordGapCenter - 274972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274972]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02202_not_prime : ¬(recordGapCenter - 274902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274902]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02203_not_prime : ¬(recordGapCenter - 274738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274738]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02204_not_prime : ¬(recordGapCenter - 274732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274732]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02205_not_prime : ¬(recordGapCenter - 274678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274678]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02206_not_prime : ¬(recordGapCenter - 274578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274578]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02207_not_prime : ¬(recordGapCenter - 274558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274558]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02208_not_prime : ¬(recordGapCenter - 274402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274402]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02209_not_prime : ¬(recordGapCenter - 274242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274242]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02210_not_prime : ¬(recordGapCenter - 274084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 274084]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02211_not_prime : ¬(recordGapCenter - 273982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273982]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02212_not_prime : ¬(recordGapCenter - 273748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273748]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02213_not_prime : ¬(recordGapCenter - 273682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273682]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02214_not_prime : ¬(recordGapCenter - 273622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273622]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02215_not_prime : ¬(recordGapCenter - 273538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273538]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02216_not_prime : ¬(recordGapCenter - 273534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273534]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02217_not_prime : ¬(recordGapCenter - 273502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273502]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02218_not_prime : ¬(recordGapCenter - 273454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273454]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02219_not_prime : ¬(recordGapCenter - 273318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273318]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02220_not_prime : ¬(recordGapCenter - 273214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273214]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02221_not_prime : ¬(recordGapCenter - 273198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273198]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02222_not_prime : ¬(recordGapCenter - 273018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 273018]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02223_not_prime : ¬(recordGapCenter - 272962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 272962]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02224_not_prime : ¬(recordGapCenter - 272908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 272908]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02225_not_prime : ¬(recordGapCenter - 272638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 272638]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02226_not_prime : ¬(recordGapCenter - 272284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 272284]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02227_not_prime : ¬(recordGapCenter - 272262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 272262]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02228_not_prime : ¬(recordGapCenter - 272212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 272212]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02229_not_prime : ¬(recordGapCenter - 272092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 272092]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02230_not_prime : ¬(recordGapCenter - 271974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271974]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02231_not_prime : ¬(recordGapCenter - 271954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271954]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02232_not_prime : ¬(recordGapCenter - 271948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271948]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02233_not_prime : ¬(recordGapCenter - 271914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271914]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02234_not_prime : ¬(recordGapCenter - 271842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271842]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02235_not_prime : ¬(recordGapCenter - 271798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271798]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02236_not_prime : ¬(recordGapCenter - 271758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271758]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02237_not_prime : ¬(recordGapCenter - 271732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271732]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02238_not_prime : ¬(recordGapCenter - 271578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271578]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02239_not_prime : ¬(recordGapCenter - 271564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271564]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

theorem fullRecordGapTerm02240_not_prime : ¬(recordGapCenter - 271554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 271554]
  · apply fullRecordGapRow00035_fermat
    simp [fullRecordGapRow00035_values]

end PrimeFactorUnimodality
