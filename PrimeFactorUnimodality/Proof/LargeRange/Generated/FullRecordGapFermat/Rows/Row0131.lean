import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00131_values : List Nat :=
  [fullRecordGapCenterValue + 492438,
    fullRecordGapCenterValue + 492482,
    fullRecordGapCenterValue + 492542,
    fullRecordGapCenterValue + 492782,
    fullRecordGapCenterValue + 492800,
    fullRecordGapCenterValue + 492836,
    fullRecordGapCenterValue + 492846,
    fullRecordGapCenterValue + 492872,
    fullRecordGapCenterValue + 492878,
    fullRecordGapCenterValue + 492956,
    fullRecordGapCenterValue + 493098,
    fullRecordGapCenterValue + 493158,
    fullRecordGapCenterValue + 493242,
    fullRecordGapCenterValue + 493418,
    fullRecordGapCenterValue + 493446,
    fullRecordGapCenterValue + 493448,
    fullRecordGapCenterValue + 493628,
    fullRecordGapCenterValue + 493670,
    fullRecordGapCenterValue + 493806,
    fullRecordGapCenterValue + 493832,
    fullRecordGapCenterValue + 493838,
    fullRecordGapCenterValue + 493958,
    fullRecordGapCenterValue + 494198,
    fullRecordGapCenterValue + 494282,
    fullRecordGapCenterValue + 494322,
    fullRecordGapCenterValue + 494330,
    fullRecordGapCenterValue + 494366,
    fullRecordGapCenterValue + 494618,
    fullRecordGapCenterValue + 494630,
    fullRecordGapCenterValue + 494762,
    fullRecordGapCenterValue + 494828,
    fullRecordGapCenterValue + 494898,
    fullRecordGapCenterValue + 495000,
    fullRecordGapCenterValue + 495038,
    fullRecordGapCenterValue + 495182,
    fullRecordGapCenterValue + 495206,
    fullRecordGapCenterValue + 495218,
    fullRecordGapCenterValue + 495230,
    fullRecordGapCenterValue + 495272,
    fullRecordGapCenterValue + 495290,
    fullRecordGapCenterValue + 495302,
    fullRecordGapCenterValue + 495332,
    fullRecordGapCenterValue + 495386,
    fullRecordGapCenterValue + 495402,
    fullRecordGapCenterValue + 495426,
    fullRecordGapCenterValue + 495692,
    fullRecordGapCenterValue + 495758,
    fullRecordGapCenterValue + 495798,
    fullRecordGapCenterValue + 495848,
    fullRecordGapCenterValue + 496130,
    fullRecordGapCenterValue + 496142,
    fullRecordGapCenterValue + 496178,
    fullRecordGapCenterValue + 496238,
    fullRecordGapCenterValue + 496268,
    fullRecordGapCenterValue + 496326,
    fullRecordGapCenterValue + 496358,
    fullRecordGapCenterValue + 496406,
    fullRecordGapCenterValue + 496532,
    fullRecordGapCenterValue + 496542,
    fullRecordGapCenterValue + 496556,
    fullRecordGapCenterValue + 496568,
    fullRecordGapCenterValue + 496598,
    fullRecordGapCenterValue + 496722,
    fullRecordGapCenterValue + 496802]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00131_fermat : ∀ n ∈ fullRecordGapRow00131_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08321_not_prime : ¬(recordGapCenter + 492438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492438]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08322_not_prime : ¬(recordGapCenter + 492482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492482]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08323_not_prime : ¬(recordGapCenter + 492542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492542]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08324_not_prime : ¬(recordGapCenter + 492782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492782]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08325_not_prime : ¬(recordGapCenter + 492800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492800]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08326_not_prime : ¬(recordGapCenter + 492836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492836]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08327_not_prime : ¬(recordGapCenter + 492846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492846]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08328_not_prime : ¬(recordGapCenter + 492872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492872]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08329_not_prime : ¬(recordGapCenter + 492878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492878]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08330_not_prime : ¬(recordGapCenter + 492956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492956]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08331_not_prime : ¬(recordGapCenter + 493098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493098]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08332_not_prime : ¬(recordGapCenter + 493158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493158]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08333_not_prime : ¬(recordGapCenter + 493242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493242]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08334_not_prime : ¬(recordGapCenter + 493418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493418]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08335_not_prime : ¬(recordGapCenter + 493446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493446]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08336_not_prime : ¬(recordGapCenter + 493448).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493448]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08337_not_prime : ¬(recordGapCenter + 493628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493628]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08338_not_prime : ¬(recordGapCenter + 493670).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493670]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08339_not_prime : ¬(recordGapCenter + 493806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493806]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08340_not_prime : ¬(recordGapCenter + 493832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493832]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08341_not_prime : ¬(recordGapCenter + 493838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493838]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08342_not_prime : ¬(recordGapCenter + 493958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493958]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08343_not_prime : ¬(recordGapCenter + 494198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494198]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08344_not_prime : ¬(recordGapCenter + 494282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494282]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08345_not_prime : ¬(recordGapCenter + 494322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494322]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08346_not_prime : ¬(recordGapCenter + 494330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494330]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08347_not_prime : ¬(recordGapCenter + 494366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494366]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08348_not_prime : ¬(recordGapCenter + 494618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494618]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08349_not_prime : ¬(recordGapCenter + 494630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494630]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08350_not_prime : ¬(recordGapCenter + 494762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494762]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08351_not_prime : ¬(recordGapCenter + 494828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494828]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08352_not_prime : ¬(recordGapCenter + 494898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494898]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08353_not_prime : ¬(recordGapCenter + 495000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495000]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08354_not_prime : ¬(recordGapCenter + 495038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495038]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08355_not_prime : ¬(recordGapCenter + 495182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495182]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08356_not_prime : ¬(recordGapCenter + 495206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495206]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08357_not_prime : ¬(recordGapCenter + 495218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495218]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08358_not_prime : ¬(recordGapCenter + 495230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495230]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08359_not_prime : ¬(recordGapCenter + 495272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495272]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08360_not_prime : ¬(recordGapCenter + 495290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495290]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08361_not_prime : ¬(recordGapCenter + 495302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495302]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08362_not_prime : ¬(recordGapCenter + 495332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495332]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08363_not_prime : ¬(recordGapCenter + 495386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495386]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08364_not_prime : ¬(recordGapCenter + 495402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495402]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08365_not_prime : ¬(recordGapCenter + 495426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495426]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08366_not_prime : ¬(recordGapCenter + 495692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495692]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08367_not_prime : ¬(recordGapCenter + 495758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495758]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08368_not_prime : ¬(recordGapCenter + 495798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495798]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08369_not_prime : ¬(recordGapCenter + 495848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495848]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08370_not_prime : ¬(recordGapCenter + 496130).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496130]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08371_not_prime : ¬(recordGapCenter + 496142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496142]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08372_not_prime : ¬(recordGapCenter + 496178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496178]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08373_not_prime : ¬(recordGapCenter + 496238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496238]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08374_not_prime : ¬(recordGapCenter + 496268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496268]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08375_not_prime : ¬(recordGapCenter + 496326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496326]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08376_not_prime : ¬(recordGapCenter + 496358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496358]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08377_not_prime : ¬(recordGapCenter + 496406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496406]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08378_not_prime : ¬(recordGapCenter + 496532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496532]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08379_not_prime : ¬(recordGapCenter + 496542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496542]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08380_not_prime : ¬(recordGapCenter + 496556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496556]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08381_not_prime : ¬(recordGapCenter + 496568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496568]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08382_not_prime : ¬(recordGapCenter + 496598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496598]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08383_not_prime : ¬(recordGapCenter + 496722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496722]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

theorem fullRecordGapTerm08384_not_prime : ¬(recordGapCenter + 496802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496802]
  · apply fullRecordGapRow00131_fermat
    simp [fullRecordGapRow00131_values]

end PrimeFactorUnimodality
