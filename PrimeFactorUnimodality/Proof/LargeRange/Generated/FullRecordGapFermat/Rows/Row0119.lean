import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00119_values : List Nat :=
  [fullRecordGapCenterValue + 437442,
    fullRecordGapCenterValue + 437498,
    fullRecordGapCenterValue + 437516,
    fullRecordGapCenterValue + 437538,
    fullRecordGapCenterValue + 437588,
    fullRecordGapCenterValue + 437678,
    fullRecordGapCenterValue + 437732,
    fullRecordGapCenterValue + 437768,
    fullRecordGapCenterValue + 437816,
    fullRecordGapCenterValue + 437838,
    fullRecordGapCenterValue + 437876,
    fullRecordGapCenterValue + 438182,
    fullRecordGapCenterValue + 438188,
    fullRecordGapCenterValue + 438222,
    fullRecordGapCenterValue + 438296,
    fullRecordGapCenterValue + 438356,
    fullRecordGapCenterValue + 438378,
    fullRecordGapCenterValue + 438392,
    fullRecordGapCenterValue + 438722,
    fullRecordGapCenterValue + 438726,
    fullRecordGapCenterValue + 438846,
    fullRecordGapCenterValue + 438926,
    fullRecordGapCenterValue + 439086,
    fullRecordGapCenterValue + 439230,
    fullRecordGapCenterValue + 439316,
    fullRecordGapCenterValue + 439352,
    fullRecordGapCenterValue + 439430,
    fullRecordGapCenterValue + 439442,
    fullRecordGapCenterValue + 439458,
    fullRecordGapCenterValue + 439598,
    fullRecordGapCenterValue + 439646,
    fullRecordGapCenterValue + 439652,
    fullRecordGapCenterValue + 439832,
    fullRecordGapCenterValue + 439862,
    fullRecordGapCenterValue + 439910,
    fullRecordGapCenterValue + 439962,
    fullRecordGapCenterValue + 440072,
    fullRecordGapCenterValue + 440178,
    fullRecordGapCenterValue + 440210,
    fullRecordGapCenterValue + 440246,
    fullRecordGapCenterValue + 440408,
    fullRecordGapCenterValue + 440456,
    fullRecordGapCenterValue + 440718,
    fullRecordGapCenterValue + 440738,
    fullRecordGapCenterValue + 440798,
    fullRecordGapCenterValue + 440822,
    fullRecordGapCenterValue + 440826,
    fullRecordGapCenterValue + 440862,
    fullRecordGapCenterValue + 441102,
    fullRecordGapCenterValue + 441110,
    fullRecordGapCenterValue + 441282,
    fullRecordGapCenterValue + 441290,
    fullRecordGapCenterValue + 441318,
    fullRecordGapCenterValue + 441362,
    fullRecordGapCenterValue + 441366,
    fullRecordGapCenterValue + 441542,
    fullRecordGapCenterValue + 441578,
    fullRecordGapCenterValue + 441582,
    fullRecordGapCenterValue + 441722,
    fullRecordGapCenterValue + 441746,
    fullRecordGapCenterValue + 441758,
    fullRecordGapCenterValue + 441806,
    fullRecordGapCenterValue + 441858,
    fullRecordGapCenterValue + 441906]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00119_fermat : ∀ n ∈ fullRecordGapRow00119_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07553_not_prime : ¬(recordGapCenter + 437442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437442]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07554_not_prime : ¬(recordGapCenter + 437498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437498]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07555_not_prime : ¬(recordGapCenter + 437516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437516]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07556_not_prime : ¬(recordGapCenter + 437538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437538]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07557_not_prime : ¬(recordGapCenter + 437588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437588]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07558_not_prime : ¬(recordGapCenter + 437678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437678]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07559_not_prime : ¬(recordGapCenter + 437732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437732]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07560_not_prime : ¬(recordGapCenter + 437768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437768]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07561_not_prime : ¬(recordGapCenter + 437816).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437816]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07562_not_prime : ¬(recordGapCenter + 437838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437838]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07563_not_prime : ¬(recordGapCenter + 437876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 437876]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07564_not_prime : ¬(recordGapCenter + 438182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 438182]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07565_not_prime : ¬(recordGapCenter + 438188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 438188]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07566_not_prime : ¬(recordGapCenter + 438222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 438222]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07567_not_prime : ¬(recordGapCenter + 438296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 438296]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07568_not_prime : ¬(recordGapCenter + 438356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 438356]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07569_not_prime : ¬(recordGapCenter + 438378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 438378]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07570_not_prime : ¬(recordGapCenter + 438392).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 438392]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07571_not_prime : ¬(recordGapCenter + 438722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 438722]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07572_not_prime : ¬(recordGapCenter + 438726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 438726]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07573_not_prime : ¬(recordGapCenter + 438846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 438846]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07574_not_prime : ¬(recordGapCenter + 438926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 438926]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07575_not_prime : ¬(recordGapCenter + 439086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 439086]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07576_not_prime : ¬(recordGapCenter + 439230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 439230]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07577_not_prime : ¬(recordGapCenter + 439316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 439316]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07578_not_prime : ¬(recordGapCenter + 439352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 439352]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07579_not_prime : ¬(recordGapCenter + 439430).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 439430]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07580_not_prime : ¬(recordGapCenter + 439442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 439442]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07581_not_prime : ¬(recordGapCenter + 439458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 439458]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07582_not_prime : ¬(recordGapCenter + 439598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 439598]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07583_not_prime : ¬(recordGapCenter + 439646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 439646]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07584_not_prime : ¬(recordGapCenter + 439652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 439652]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07585_not_prime : ¬(recordGapCenter + 439832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 439832]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07586_not_prime : ¬(recordGapCenter + 439862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 439862]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07587_not_prime : ¬(recordGapCenter + 439910).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 439910]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07588_not_prime : ¬(recordGapCenter + 439962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 439962]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07589_not_prime : ¬(recordGapCenter + 440072).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 440072]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07590_not_prime : ¬(recordGapCenter + 440178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 440178]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07591_not_prime : ¬(recordGapCenter + 440210).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 440210]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07592_not_prime : ¬(recordGapCenter + 440246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 440246]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07593_not_prime : ¬(recordGapCenter + 440408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 440408]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07594_not_prime : ¬(recordGapCenter + 440456).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 440456]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07595_not_prime : ¬(recordGapCenter + 440718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 440718]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07596_not_prime : ¬(recordGapCenter + 440738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 440738]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07597_not_prime : ¬(recordGapCenter + 440798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 440798]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07598_not_prime : ¬(recordGapCenter + 440822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 440822]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07599_not_prime : ¬(recordGapCenter + 440826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 440826]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07600_not_prime : ¬(recordGapCenter + 440862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 440862]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07601_not_prime : ¬(recordGapCenter + 441102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441102]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07602_not_prime : ¬(recordGapCenter + 441110).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441110]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07603_not_prime : ¬(recordGapCenter + 441282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441282]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07604_not_prime : ¬(recordGapCenter + 441290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441290]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07605_not_prime : ¬(recordGapCenter + 441318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441318]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07606_not_prime : ¬(recordGapCenter + 441362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441362]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07607_not_prime : ¬(recordGapCenter + 441366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441366]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07608_not_prime : ¬(recordGapCenter + 441542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441542]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07609_not_prime : ¬(recordGapCenter + 441578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441578]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07610_not_prime : ¬(recordGapCenter + 441582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441582]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07611_not_prime : ¬(recordGapCenter + 441722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441722]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07612_not_prime : ¬(recordGapCenter + 441746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441746]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07613_not_prime : ¬(recordGapCenter + 441758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441758]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07614_not_prime : ¬(recordGapCenter + 441806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441806]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07615_not_prime : ¬(recordGapCenter + 441858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441858]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

theorem fullRecordGapTerm07616_not_prime : ¬(recordGapCenter + 441906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441906]
  · apply fullRecordGapRow00119_fermat
    simp [fullRecordGapRow00119_values]

end PrimeFactorUnimodality
