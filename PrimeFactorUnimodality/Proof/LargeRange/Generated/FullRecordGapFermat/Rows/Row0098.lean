import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00098_values : List Nat :=
  [fullRecordGapCenterValue + 332466,
    fullRecordGapCenterValue + 332468,
    fullRecordGapCenterValue + 332708,
    fullRecordGapCenterValue + 332798,
    fullRecordGapCenterValue + 332858,
    fullRecordGapCenterValue + 332876,
    fullRecordGapCenterValue + 332942,
    fullRecordGapCenterValue + 333068,
    fullRecordGapCenterValue + 333246,
    fullRecordGapCenterValue + 333338,
    fullRecordGapCenterValue + 333446,
    fullRecordGapCenterValue + 333618,
    fullRecordGapCenterValue + 333698,
    fullRecordGapCenterValue + 333722,
    fullRecordGapCenterValue + 333786,
    fullRecordGapCenterValue + 333798,
    fullRecordGapCenterValue + 333818,
    fullRecordGapCenterValue + 333966,
    fullRecordGapCenterValue + 334148,
    fullRecordGapCenterValue + 334346,
    fullRecordGapCenterValue + 334388,
    fullRecordGapCenterValue + 334398,
    fullRecordGapCenterValue + 334556,
    fullRecordGapCenterValue + 334622,
    fullRecordGapCenterValue + 334652,
    fullRecordGapCenterValue + 334868,
    fullRecordGapCenterValue + 334982,
    fullRecordGapCenterValue + 335058,
    fullRecordGapCenterValue + 335186,
    fullRecordGapCenterValue + 335252,
    fullRecordGapCenterValue + 335366,
    fullRecordGapCenterValue + 335372,
    fullRecordGapCenterValue + 335406,
    fullRecordGapCenterValue + 335598,
    fullRecordGapCenterValue + 335732,
    fullRecordGapCenterValue + 335756,
    fullRecordGapCenterValue + 335876,
    fullRecordGapCenterValue + 335906,
    fullRecordGapCenterValue + 335982,
    fullRecordGapCenterValue + 336018,
    fullRecordGapCenterValue + 336026,
    fullRecordGapCenterValue + 336086,
    fullRecordGapCenterValue + 336236,
    fullRecordGapCenterValue + 336506,
    fullRecordGapCenterValue + 336522,
    fullRecordGapCenterValue + 336548,
    fullRecordGapCenterValue + 336558,
    fullRecordGapCenterValue + 336606,
    fullRecordGapCenterValue + 336738,
    fullRecordGapCenterValue + 336798,
    fullRecordGapCenterValue + 336956,
    fullRecordGapCenterValue + 336962,
    fullRecordGapCenterValue + 336998,
    fullRecordGapCenterValue + 337026,
    fullRecordGapCenterValue + 337118,
    fullRecordGapCenterValue + 337242,
    fullRecordGapCenterValue + 337286,
    fullRecordGapCenterValue + 337422,
    fullRecordGapCenterValue + 337500,
    fullRecordGapCenterValue + 337556,
    fullRecordGapCenterValue + 337562,
    fullRecordGapCenterValue + 337802,
    fullRecordGapCenterValue + 338126,
    fullRecordGapCenterValue + 338138]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00098_fermat : ∀ n ∈ fullRecordGapRow00098_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06209_not_prime : ¬(recordGapCenter + 332466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 332466]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06210_not_prime : ¬(recordGapCenter + 332468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 332468]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06211_not_prime : ¬(recordGapCenter + 332708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 332708]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06212_not_prime : ¬(recordGapCenter + 332798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 332798]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06213_not_prime : ¬(recordGapCenter + 332858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 332858]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06214_not_prime : ¬(recordGapCenter + 332876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 332876]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06215_not_prime : ¬(recordGapCenter + 332942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 332942]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06216_not_prime : ¬(recordGapCenter + 333068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 333068]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06217_not_prime : ¬(recordGapCenter + 333246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 333246]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06218_not_prime : ¬(recordGapCenter + 333338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 333338]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06219_not_prime : ¬(recordGapCenter + 333446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 333446]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06220_not_prime : ¬(recordGapCenter + 333618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 333618]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06221_not_prime : ¬(recordGapCenter + 333698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 333698]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06222_not_prime : ¬(recordGapCenter + 333722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 333722]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06223_not_prime : ¬(recordGapCenter + 333786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 333786]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06224_not_prime : ¬(recordGapCenter + 333798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 333798]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06225_not_prime : ¬(recordGapCenter + 333818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 333818]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06226_not_prime : ¬(recordGapCenter + 333966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 333966]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06227_not_prime : ¬(recordGapCenter + 334148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 334148]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06228_not_prime : ¬(recordGapCenter + 334346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 334346]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06229_not_prime : ¬(recordGapCenter + 334388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 334388]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06230_not_prime : ¬(recordGapCenter + 334398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 334398]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06231_not_prime : ¬(recordGapCenter + 334556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 334556]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06232_not_prime : ¬(recordGapCenter + 334622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 334622]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06233_not_prime : ¬(recordGapCenter + 334652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 334652]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06234_not_prime : ¬(recordGapCenter + 334868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 334868]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06235_not_prime : ¬(recordGapCenter + 334982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 334982]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06236_not_prime : ¬(recordGapCenter + 335058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 335058]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06237_not_prime : ¬(recordGapCenter + 335186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 335186]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06238_not_prime : ¬(recordGapCenter + 335252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 335252]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06239_not_prime : ¬(recordGapCenter + 335366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 335366]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06240_not_prime : ¬(recordGapCenter + 335372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 335372]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06241_not_prime : ¬(recordGapCenter + 335406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 335406]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06242_not_prime : ¬(recordGapCenter + 335598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 335598]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06243_not_prime : ¬(recordGapCenter + 335732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 335732]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06244_not_prime : ¬(recordGapCenter + 335756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 335756]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06245_not_prime : ¬(recordGapCenter + 335876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 335876]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06246_not_prime : ¬(recordGapCenter + 335906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 335906]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06247_not_prime : ¬(recordGapCenter + 335982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 335982]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06248_not_prime : ¬(recordGapCenter + 336018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336018]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06249_not_prime : ¬(recordGapCenter + 336026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336026]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06250_not_prime : ¬(recordGapCenter + 336086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336086]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06251_not_prime : ¬(recordGapCenter + 336236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336236]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06252_not_prime : ¬(recordGapCenter + 336506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336506]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06253_not_prime : ¬(recordGapCenter + 336522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336522]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06254_not_prime : ¬(recordGapCenter + 336548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336548]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06255_not_prime : ¬(recordGapCenter + 336558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336558]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06256_not_prime : ¬(recordGapCenter + 336606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336606]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06257_not_prime : ¬(recordGapCenter + 336738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336738]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06258_not_prime : ¬(recordGapCenter + 336798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336798]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06259_not_prime : ¬(recordGapCenter + 336956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336956]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06260_not_prime : ¬(recordGapCenter + 336962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336962]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06261_not_prime : ¬(recordGapCenter + 336998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 336998]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06262_not_prime : ¬(recordGapCenter + 337026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 337026]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06263_not_prime : ¬(recordGapCenter + 337118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 337118]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06264_not_prime : ¬(recordGapCenter + 337242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 337242]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06265_not_prime : ¬(recordGapCenter + 337286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 337286]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06266_not_prime : ¬(recordGapCenter + 337422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 337422]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06267_not_prime : ¬(recordGapCenter + 337500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 337500]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06268_not_prime : ¬(recordGapCenter + 337556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 337556]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06269_not_prime : ¬(recordGapCenter + 337562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 337562]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06270_not_prime : ¬(recordGapCenter + 337802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 337802]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06271_not_prime : ¬(recordGapCenter + 338126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 338126]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

theorem fullRecordGapTerm06272_not_prime : ¬(recordGapCenter + 338138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 338138]
  · apply fullRecordGapRow00098_fermat
    simp [fullRecordGapRow00098_values]

end PrimeFactorUnimodality
