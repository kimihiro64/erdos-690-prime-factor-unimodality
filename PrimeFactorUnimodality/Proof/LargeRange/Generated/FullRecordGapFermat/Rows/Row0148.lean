import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00148_values : List Nat :=
  [fullRecordGapCenterValue + 564042,
    fullRecordGapCenterValue + 564056,
    fullRecordGapCenterValue + 564092,
    fullRecordGapCenterValue + 564342,
    fullRecordGapCenterValue + 564392,
    fullRecordGapCenterValue + 564506,
    fullRecordGapCenterValue + 564666,
    fullRecordGapCenterValue + 564702,
    fullRecordGapCenterValue + 564726,
    fullRecordGapCenterValue + 564782,
    fullRecordGapCenterValue + 564918,
    fullRecordGapCenterValue + 564986,
    fullRecordGapCenterValue + 565052,
    fullRecordGapCenterValue + 565076,
    fullRecordGapCenterValue + 565112,
    fullRecordGapCenterValue + 565178,
    fullRecordGapCenterValue + 565190,
    fullRecordGapCenterValue + 565310,
    fullRecordGapCenterValue + 565332,
    fullRecordGapCenterValue + 565406,
    fullRecordGapCenterValue + 565518,
    fullRecordGapCenterValue + 565538,
    fullRecordGapCenterValue + 565566,
    fullRecordGapCenterValue + 565652,
    fullRecordGapCenterValue + 565716,
    fullRecordGapCenterValue + 565772,
    fullRecordGapCenterValue + 565826,
    fullRecordGapCenterValue + 565832,
    fullRecordGapCenterValue + 565932,
    fullRecordGapCenterValue + 565950,
    fullRecordGapCenterValue + 565962,
    fullRecordGapCenterValue + 566018,
    fullRecordGapCenterValue + 566036,
    fullRecordGapCenterValue + 566058,
    fullRecordGapCenterValue + 566102,
    fullRecordGapCenterValue + 566330,
    fullRecordGapCenterValue + 566366,
    fullRecordGapCenterValue + 566382,
    fullRecordGapCenterValue + 566526,
    fullRecordGapCenterValue + 566598,
    fullRecordGapCenterValue + 566682,
    fullRecordGapCenterValue + 566708,
    fullRecordGapCenterValue + 566756,
    fullRecordGapCenterValue + 566778,
    fullRecordGapCenterValue + 566862,
    fullRecordGapCenterValue + 566898,
    fullRecordGapCenterValue + 567032,
    fullRecordGapCenterValue + 567110,
    fullRecordGapCenterValue + 567128,
    fullRecordGapCenterValue + 567186,
    fullRecordGapCenterValue + 567338,
    fullRecordGapCenterValue + 567366,
    fullRecordGapCenterValue + 567470,
    fullRecordGapCenterValue + 567498,
    fullRecordGapCenterValue + 567752,
    fullRecordGapCenterValue + 567830,
    fullRecordGapCenterValue + 568068,
    fullRecordGapCenterValue + 568118,
    fullRecordGapCenterValue + 568130,
    fullRecordGapCenterValue + 568236,
    fullRecordGapCenterValue + 568268,
    fullRecordGapCenterValue + 568298,
    fullRecordGapCenterValue + 568382,
    fullRecordGapCenterValue + 568482]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00148_fermat : ∀ n ∈ fullRecordGapRow00148_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09409_not_prime : ¬(recordGapCenter + 564042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 564042]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09410_not_prime : ¬(recordGapCenter + 564056).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 564056]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09411_not_prime : ¬(recordGapCenter + 564092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 564092]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09412_not_prime : ¬(recordGapCenter + 564342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 564342]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09413_not_prime : ¬(recordGapCenter + 564392).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 564392]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09414_not_prime : ¬(recordGapCenter + 564506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 564506]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09415_not_prime : ¬(recordGapCenter + 564666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 564666]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09416_not_prime : ¬(recordGapCenter + 564702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 564702]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09417_not_prime : ¬(recordGapCenter + 564726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 564726]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09418_not_prime : ¬(recordGapCenter + 564782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 564782]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09419_not_prime : ¬(recordGapCenter + 564918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 564918]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09420_not_prime : ¬(recordGapCenter + 564986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 564986]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09421_not_prime : ¬(recordGapCenter + 565052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565052]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09422_not_prime : ¬(recordGapCenter + 565076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565076]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09423_not_prime : ¬(recordGapCenter + 565112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565112]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09424_not_prime : ¬(recordGapCenter + 565178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565178]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09425_not_prime : ¬(recordGapCenter + 565190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565190]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09426_not_prime : ¬(recordGapCenter + 565310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565310]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09427_not_prime : ¬(recordGapCenter + 565332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565332]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09428_not_prime : ¬(recordGapCenter + 565406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565406]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09429_not_prime : ¬(recordGapCenter + 565518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565518]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09430_not_prime : ¬(recordGapCenter + 565538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565538]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09431_not_prime : ¬(recordGapCenter + 565566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565566]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09432_not_prime : ¬(recordGapCenter + 565652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565652]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09433_not_prime : ¬(recordGapCenter + 565716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565716]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09434_not_prime : ¬(recordGapCenter + 565772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565772]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09435_not_prime : ¬(recordGapCenter + 565826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565826]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09436_not_prime : ¬(recordGapCenter + 565832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565832]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09437_not_prime : ¬(recordGapCenter + 565932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565932]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09438_not_prime : ¬(recordGapCenter + 565950).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565950]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09439_not_prime : ¬(recordGapCenter + 565962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 565962]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09440_not_prime : ¬(recordGapCenter + 566018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566018]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09441_not_prime : ¬(recordGapCenter + 566036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566036]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09442_not_prime : ¬(recordGapCenter + 566058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566058]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09443_not_prime : ¬(recordGapCenter + 566102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566102]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09444_not_prime : ¬(recordGapCenter + 566330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566330]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09445_not_prime : ¬(recordGapCenter + 566366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566366]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09446_not_prime : ¬(recordGapCenter + 566382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566382]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09447_not_prime : ¬(recordGapCenter + 566526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566526]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09448_not_prime : ¬(recordGapCenter + 566598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566598]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09449_not_prime : ¬(recordGapCenter + 566682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566682]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09450_not_prime : ¬(recordGapCenter + 566708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566708]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09451_not_prime : ¬(recordGapCenter + 566756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566756]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09452_not_prime : ¬(recordGapCenter + 566778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566778]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09453_not_prime : ¬(recordGapCenter + 566862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566862]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09454_not_prime : ¬(recordGapCenter + 566898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 566898]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09455_not_prime : ¬(recordGapCenter + 567032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 567032]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09456_not_prime : ¬(recordGapCenter + 567110).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 567110]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09457_not_prime : ¬(recordGapCenter + 567128).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 567128]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09458_not_prime : ¬(recordGapCenter + 567186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 567186]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09459_not_prime : ¬(recordGapCenter + 567338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 567338]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09460_not_prime : ¬(recordGapCenter + 567366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 567366]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09461_not_prime : ¬(recordGapCenter + 567470).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 567470]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09462_not_prime : ¬(recordGapCenter + 567498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 567498]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09463_not_prime : ¬(recordGapCenter + 567752).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 567752]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09464_not_prime : ¬(recordGapCenter + 567830).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 567830]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09465_not_prime : ¬(recordGapCenter + 568068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 568068]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09466_not_prime : ¬(recordGapCenter + 568118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 568118]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09467_not_prime : ¬(recordGapCenter + 568130).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 568130]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09468_not_prime : ¬(recordGapCenter + 568236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 568236]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09469_not_prime : ¬(recordGapCenter + 568268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 568268]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09470_not_prime : ¬(recordGapCenter + 568298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 568298]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09471_not_prime : ¬(recordGapCenter + 568382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 568382]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

theorem fullRecordGapTerm09472_not_prime : ¬(recordGapCenter + 568482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 568482]
  · apply fullRecordGapRow00148_fermat
    simp [fullRecordGapRow00148_values]

end PrimeFactorUnimodality
