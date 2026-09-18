import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00033_values : List Nat :=
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
    fullRecordGapCenterValue + 487748,
    fullRecordGapCenterValue + 487790,
    fullRecordGapCenterValue + 487796,
    fullRecordGapCenterValue + 487842,
    fullRecordGapCenterValue + 487946,
    fullRecordGapCenterValue + 488090,
    fullRecordGapCenterValue + 488216,
    fullRecordGapCenterValue + 488276,
    fullRecordGapCenterValue + 488282,
    fullRecordGapCenterValue + 488318,
    fullRecordGapCenterValue + 488468,
    fullRecordGapCenterValue + 488526,
    fullRecordGapCenterValue + 488582,
    fullRecordGapCenterValue + 488666,
    fullRecordGapCenterValue + 488678,
    fullRecordGapCenterValue + 488702,
    fullRecordGapCenterValue + 488762,
    fullRecordGapCenterValue + 488786,
    fullRecordGapCenterValue + 488822,
    fullRecordGapCenterValue + 488828,
    fullRecordGapCenterValue + 488876,
    fullRecordGapCenterValue + 489092,
    fullRecordGapCenterValue + 489198,
    fullRecordGapCenterValue + 489282,
    fullRecordGapCenterValue + 489318,
    fullRecordGapCenterValue + 489378,
    fullRecordGapCenterValue + 489506,
    fullRecordGapCenterValue + 489548,
    fullRecordGapCenterValue + 489882,
    fullRecordGapCenterValue + 489890,
    fullRecordGapCenterValue + 490026,
    fullRecordGapCenterValue + 490058,
    fullRecordGapCenterValue + 490206,
    fullRecordGapCenterValue + 490316,
    fullRecordGapCenterValue + 490346,
    fullRecordGapCenterValue + 490362,
    fullRecordGapCenterValue + 490436,
    fullRecordGapCenterValue + 490502,
    fullRecordGapCenterValue + 490598,
    fullRecordGapCenterValue + 490638,
    fullRecordGapCenterValue + 490712,
    fullRecordGapCenterValue + 490766,
    fullRecordGapCenterValue + 490856,
    fullRecordGapCenterValue + 491012,
    fullRecordGapCenterValue + 491030,
    fullRecordGapCenterValue + 491090,
    fullRecordGapCenterValue + 491258,
    fullRecordGapCenterValue + 491298,
    fullRecordGapCenterValue + 491306,
    fullRecordGapCenterValue + 491396,
    fullRecordGapCenterValue + 491528,
    fullRecordGapCenterValue + 491570,
    fullRecordGapCenterValue + 491702,
    fullRecordGapCenterValue + 491726,
    fullRecordGapCenterValue + 491822,
    fullRecordGapCenterValue + 491838,
    fullRecordGapCenterValue + 491930,
    fullRecordGapCenterValue + 492068,
    fullRecordGapCenterValue + 492146,
    fullRecordGapCenterValue + 492186,
    fullRecordGapCenterValue + 492230,
    fullRecordGapCenterValue + 492266,
    fullRecordGapCenterValue + 492306,
    fullRecordGapCenterValue + 492308,
    fullRecordGapCenterValue + 492332,
    fullRecordGapCenterValue + 492438,
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
    fullRecordGapCenterValue + 496802,
    fullRecordGapCenterValue + 497066,
    fullRecordGapCenterValue + 497298,
    fullRecordGapCenterValue + 497348,
    fullRecordGapCenterValue + 497390,
    fullRecordGapCenterValue + 497418,
    fullRecordGapCenterValue + 497498,
    fullRecordGapCenterValue + 497732,
    fullRecordGapCenterValue + 497738,
    fullRecordGapCenterValue + 497786,
    fullRecordGapCenterValue + 497870,
    fullRecordGapCenterValue + 498036,
    fullRecordGapCenterValue + 498282,
    fullRecordGapCenterValue + 498398,
    fullRecordGapCenterValue + 498558,
    fullRecordGapCenterValue + 498572,
    fullRecordGapCenterValue + 498702,
    fullRecordGapCenterValue + 498716,
    fullRecordGapCenterValue + 498776,
    fullRecordGapCenterValue + 498842,
    fullRecordGapCenterValue + 498878,
    fullRecordGapCenterValue + 499178,
    fullRecordGapCenterValue + 499370,
    fullRecordGapCenterValue + 499412,
    fullRecordGapCenterValue + 499430,
    fullRecordGapCenterValue + 499542,
    fullRecordGapCenterValue + 499602,
    fullRecordGapCenterValue + 499676,
    fullRecordGapCenterValue + 499706,
    fullRecordGapCenterValue + 499866,
    fullRecordGapCenterValue + 499886,
    fullRecordGapCenterValue + 499916,
    fullRecordGapCenterValue + 499976,
    fullRecordGapCenterValue + 500246,
    fullRecordGapCenterValue + 500252,
    fullRecordGapCenterValue + 500312,
    fullRecordGapCenterValue + 500330,
    fullRecordGapCenterValue + 500372,
    fullRecordGapCenterValue + 500406,
    fullRecordGapCenterValue + 500468,
    fullRecordGapCenterValue + 500510,
    fullRecordGapCenterValue + 500622,
    fullRecordGapCenterValue + 500690,
    fullRecordGapCenterValue + 500876,
    fullRecordGapCenterValue + 500882,
    fullRecordGapCenterValue + 500978,
    fullRecordGapCenterValue + 501086,
    fullRecordGapCenterValue + 501110,
    fullRecordGapCenterValue + 501362,
    fullRecordGapCenterValue + 501506,
    fullRecordGapCenterValue + 501548,
    fullRecordGapCenterValue + 501590,
    fullRecordGapCenterValue + 501692,
    fullRecordGapCenterValue + 501702,
    fullRecordGapCenterValue + 501716,
    fullRecordGapCenterValue + 501770,
    fullRecordGapCenterValue + 501848,
    fullRecordGapCenterValue + 501918,
    fullRecordGapCenterValue + 501938,
    fullRecordGapCenterValue + 501986,
    fullRecordGapCenterValue + 502070,
    fullRecordGapCenterValue + 502118,
    fullRecordGapCenterValue + 502310,
    fullRecordGapCenterValue + 502406,
    fullRecordGapCenterValue + 502526]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00033_fermat : ∀ n ∈ fullRecordGapRow00033_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08193_not_prime : ¬(recordGapCenter + 483222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483222]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08194_not_prime : ¬(recordGapCenter + 483302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483302]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08195_not_prime : ¬(recordGapCenter + 483326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483326]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08196_not_prime : ¬(recordGapCenter + 483422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483422]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08197_not_prime : ¬(recordGapCenter + 483596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483596]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08198_not_prime : ¬(recordGapCenter + 483618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483618]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08199_not_prime : ¬(recordGapCenter + 483668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483668]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08200_not_prime : ¬(recordGapCenter + 483830).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483830]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08201_not_prime : ¬(recordGapCenter + 483840).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483840]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08202_not_prime : ¬(recordGapCenter + 483926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483926]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08203_not_prime : ¬(recordGapCenter + 483942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483942]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08204_not_prime : ¬(recordGapCenter + 484026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484026]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08205_not_prime : ¬(recordGapCenter + 484076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484076]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08206_not_prime : ¬(recordGapCenter + 484086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484086]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08207_not_prime : ¬(recordGapCenter + 484166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484166]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08208_not_prime : ¬(recordGapCenter + 484202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484202]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08209_not_prime : ¬(recordGapCenter + 484628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484628]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08210_not_prime : ¬(recordGapCenter + 484712).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484712]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08211_not_prime : ¬(recordGapCenter + 484982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484982]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08212_not_prime : ¬(recordGapCenter + 484998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 484998]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08213_not_prime : ¬(recordGapCenter + 485018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485018]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08214_not_prime : ¬(recordGapCenter + 485102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485102]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08215_not_prime : ¬(recordGapCenter + 485178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485178]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08216_not_prime : ¬(recordGapCenter + 485252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485252]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08217_not_prime : ¬(recordGapCenter + 485270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485270]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08218_not_prime : ¬(recordGapCenter + 485378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485378]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08219_not_prime : ¬(recordGapCenter + 485390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485390]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08220_not_prime : ¬(recordGapCenter + 485396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485396]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08221_not_prime : ¬(recordGapCenter + 485468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485468]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08222_not_prime : ¬(recordGapCenter + 485516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485516]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08223_not_prime : ¬(recordGapCenter + 485546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485546]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08224_not_prime : ¬(recordGapCenter + 485612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485612]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08225_not_prime : ¬(recordGapCenter + 485846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485846]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08226_not_prime : ¬(recordGapCenter + 485930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485930]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08227_not_prime : ¬(recordGapCenter + 485942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485942]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08228_not_prime : ¬(recordGapCenter + 485948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485948]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08229_not_prime : ¬(recordGapCenter + 485972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485972]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08230_not_prime : ¬(recordGapCenter + 485978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 485978]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08231_not_prime : ¬(recordGapCenter + 486000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486000]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08232_not_prime : ¬(recordGapCenter + 486182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486182]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08233_not_prime : ¬(recordGapCenter + 486188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486188]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08234_not_prime : ¬(recordGapCenter + 486236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486236]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08235_not_prime : ¬(recordGapCenter + 486258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486258]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08236_not_prime : ¬(recordGapCenter + 486462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486462]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08237_not_prime : ¬(recordGapCenter + 486488).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486488]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08238_not_prime : ¬(recordGapCenter + 486582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486582]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08239_not_prime : ¬(recordGapCenter + 486602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486602]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08240_not_prime : ¬(recordGapCenter + 486606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486606]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08241_not_prime : ¬(recordGapCenter + 486686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486686]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08242_not_prime : ¬(recordGapCenter + 486782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486782]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08243_not_prime : ¬(recordGapCenter + 486788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486788]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08244_not_prime : ¬(recordGapCenter + 486806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486806]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08245_not_prime : ¬(recordGapCenter + 486872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486872]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08246_not_prime : ¬(recordGapCenter + 486942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 486942]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08247_not_prime : ¬(recordGapCenter + 487148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487148]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08248_not_prime : ¬(recordGapCenter + 487166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487166]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08249_not_prime : ¬(recordGapCenter + 487218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487218]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08250_not_prime : ¬(recordGapCenter + 487226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487226]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08251_not_prime : ¬(recordGapCenter + 487310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487310]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08252_not_prime : ¬(recordGapCenter + 487338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487338]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08253_not_prime : ¬(recordGapCenter + 487398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487398]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08254_not_prime : ¬(recordGapCenter + 487496).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487496]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08255_not_prime : ¬(recordGapCenter + 487688).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487688]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08256_not_prime : ¬(recordGapCenter + 487748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487748]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08257_not_prime : ¬(recordGapCenter + 487790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487790]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08258_not_prime : ¬(recordGapCenter + 487796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487796]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08259_not_prime : ¬(recordGapCenter + 487842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487842]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08260_not_prime : ¬(recordGapCenter + 487946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 487946]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08261_not_prime : ¬(recordGapCenter + 488090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488090]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08262_not_prime : ¬(recordGapCenter + 488216).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488216]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08263_not_prime : ¬(recordGapCenter + 488276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488276]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08264_not_prime : ¬(recordGapCenter + 488282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488282]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08265_not_prime : ¬(recordGapCenter + 488318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488318]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08266_not_prime : ¬(recordGapCenter + 488468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488468]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08267_not_prime : ¬(recordGapCenter + 488526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488526]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08268_not_prime : ¬(recordGapCenter + 488582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488582]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08269_not_prime : ¬(recordGapCenter + 488666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488666]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08270_not_prime : ¬(recordGapCenter + 488678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488678]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08271_not_prime : ¬(recordGapCenter + 488702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488702]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08272_not_prime : ¬(recordGapCenter + 488762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488762]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08273_not_prime : ¬(recordGapCenter + 488786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488786]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08274_not_prime : ¬(recordGapCenter + 488822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488822]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08275_not_prime : ¬(recordGapCenter + 488828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488828]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08276_not_prime : ¬(recordGapCenter + 488876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 488876]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08277_not_prime : ¬(recordGapCenter + 489092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489092]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08278_not_prime : ¬(recordGapCenter + 489198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489198]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08279_not_prime : ¬(recordGapCenter + 489282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489282]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08280_not_prime : ¬(recordGapCenter + 489318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489318]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08281_not_prime : ¬(recordGapCenter + 489378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489378]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08282_not_prime : ¬(recordGapCenter + 489506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489506]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08283_not_prime : ¬(recordGapCenter + 489548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489548]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08284_not_prime : ¬(recordGapCenter + 489882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489882]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08285_not_prime : ¬(recordGapCenter + 489890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 489890]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08286_not_prime : ¬(recordGapCenter + 490026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490026]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08287_not_prime : ¬(recordGapCenter + 490058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490058]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08288_not_prime : ¬(recordGapCenter + 490206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490206]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08289_not_prime : ¬(recordGapCenter + 490316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490316]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08290_not_prime : ¬(recordGapCenter + 490346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490346]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08291_not_prime : ¬(recordGapCenter + 490362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490362]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08292_not_prime : ¬(recordGapCenter + 490436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490436]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08293_not_prime : ¬(recordGapCenter + 490502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490502]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08294_not_prime : ¬(recordGapCenter + 490598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490598]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08295_not_prime : ¬(recordGapCenter + 490638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490638]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08296_not_prime : ¬(recordGapCenter + 490712).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490712]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08297_not_prime : ¬(recordGapCenter + 490766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490766]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08298_not_prime : ¬(recordGapCenter + 490856).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 490856]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08299_not_prime : ¬(recordGapCenter + 491012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491012]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08300_not_prime : ¬(recordGapCenter + 491030).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491030]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08301_not_prime : ¬(recordGapCenter + 491090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491090]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08302_not_prime : ¬(recordGapCenter + 491258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491258]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08303_not_prime : ¬(recordGapCenter + 491298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491298]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08304_not_prime : ¬(recordGapCenter + 491306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491306]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08305_not_prime : ¬(recordGapCenter + 491396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491396]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08306_not_prime : ¬(recordGapCenter + 491528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491528]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08307_not_prime : ¬(recordGapCenter + 491570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491570]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08308_not_prime : ¬(recordGapCenter + 491702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491702]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08309_not_prime : ¬(recordGapCenter + 491726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491726]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08310_not_prime : ¬(recordGapCenter + 491822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491822]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08311_not_prime : ¬(recordGapCenter + 491838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491838]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08312_not_prime : ¬(recordGapCenter + 491930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 491930]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08313_not_prime : ¬(recordGapCenter + 492068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492068]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08314_not_prime : ¬(recordGapCenter + 492146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492146]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08315_not_prime : ¬(recordGapCenter + 492186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492186]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08316_not_prime : ¬(recordGapCenter + 492230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492230]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08317_not_prime : ¬(recordGapCenter + 492266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492266]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08318_not_prime : ¬(recordGapCenter + 492306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492306]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08319_not_prime : ¬(recordGapCenter + 492308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492308]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08320_not_prime : ¬(recordGapCenter + 492332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492332]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08321_not_prime : ¬(recordGapCenter + 492438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492438]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08322_not_prime : ¬(recordGapCenter + 492482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492482]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08323_not_prime : ¬(recordGapCenter + 492542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492542]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08324_not_prime : ¬(recordGapCenter + 492782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492782]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08325_not_prime : ¬(recordGapCenter + 492800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492800]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08326_not_prime : ¬(recordGapCenter + 492836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492836]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08327_not_prime : ¬(recordGapCenter + 492846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492846]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08328_not_prime : ¬(recordGapCenter + 492872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492872]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08329_not_prime : ¬(recordGapCenter + 492878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492878]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08330_not_prime : ¬(recordGapCenter + 492956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 492956]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08331_not_prime : ¬(recordGapCenter + 493098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493098]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08332_not_prime : ¬(recordGapCenter + 493158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493158]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08333_not_prime : ¬(recordGapCenter + 493242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493242]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08334_not_prime : ¬(recordGapCenter + 493418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493418]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08335_not_prime : ¬(recordGapCenter + 493446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493446]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08336_not_prime : ¬(recordGapCenter + 493448).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493448]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08337_not_prime : ¬(recordGapCenter + 493628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493628]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08338_not_prime : ¬(recordGapCenter + 493670).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493670]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08339_not_prime : ¬(recordGapCenter + 493806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493806]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08340_not_prime : ¬(recordGapCenter + 493832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493832]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08341_not_prime : ¬(recordGapCenter + 493838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493838]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08342_not_prime : ¬(recordGapCenter + 493958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 493958]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08343_not_prime : ¬(recordGapCenter + 494198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494198]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08344_not_prime : ¬(recordGapCenter + 494282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494282]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08345_not_prime : ¬(recordGapCenter + 494322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494322]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08346_not_prime : ¬(recordGapCenter + 494330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494330]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08347_not_prime : ¬(recordGapCenter + 494366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494366]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08348_not_prime : ¬(recordGapCenter + 494618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494618]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08349_not_prime : ¬(recordGapCenter + 494630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494630]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08350_not_prime : ¬(recordGapCenter + 494762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494762]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08351_not_prime : ¬(recordGapCenter + 494828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494828]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08352_not_prime : ¬(recordGapCenter + 494898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 494898]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08353_not_prime : ¬(recordGapCenter + 495000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495000]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08354_not_prime : ¬(recordGapCenter + 495038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495038]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08355_not_prime : ¬(recordGapCenter + 495182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495182]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08356_not_prime : ¬(recordGapCenter + 495206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495206]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08357_not_prime : ¬(recordGapCenter + 495218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495218]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08358_not_prime : ¬(recordGapCenter + 495230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495230]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08359_not_prime : ¬(recordGapCenter + 495272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495272]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08360_not_prime : ¬(recordGapCenter + 495290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495290]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08361_not_prime : ¬(recordGapCenter + 495302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495302]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08362_not_prime : ¬(recordGapCenter + 495332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495332]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08363_not_prime : ¬(recordGapCenter + 495386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495386]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08364_not_prime : ¬(recordGapCenter + 495402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495402]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08365_not_prime : ¬(recordGapCenter + 495426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495426]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08366_not_prime : ¬(recordGapCenter + 495692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495692]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08367_not_prime : ¬(recordGapCenter + 495758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495758]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08368_not_prime : ¬(recordGapCenter + 495798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495798]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08369_not_prime : ¬(recordGapCenter + 495848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 495848]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08370_not_prime : ¬(recordGapCenter + 496130).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496130]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08371_not_prime : ¬(recordGapCenter + 496142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496142]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08372_not_prime : ¬(recordGapCenter + 496178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496178]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08373_not_prime : ¬(recordGapCenter + 496238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496238]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08374_not_prime : ¬(recordGapCenter + 496268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496268]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08375_not_prime : ¬(recordGapCenter + 496326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496326]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08376_not_prime : ¬(recordGapCenter + 496358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496358]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08377_not_prime : ¬(recordGapCenter + 496406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496406]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08378_not_prime : ¬(recordGapCenter + 496532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496532]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08379_not_prime : ¬(recordGapCenter + 496542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496542]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08380_not_prime : ¬(recordGapCenter + 496556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496556]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08381_not_prime : ¬(recordGapCenter + 496568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496568]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08382_not_prime : ¬(recordGapCenter + 496598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496598]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08383_not_prime : ¬(recordGapCenter + 496722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496722]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08384_not_prime : ¬(recordGapCenter + 496802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 496802]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08385_not_prime : ¬(recordGapCenter + 497066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497066]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08386_not_prime : ¬(recordGapCenter + 497298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497298]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08387_not_prime : ¬(recordGapCenter + 497348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497348]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08388_not_prime : ¬(recordGapCenter + 497390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497390]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08389_not_prime : ¬(recordGapCenter + 497418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497418]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08390_not_prime : ¬(recordGapCenter + 497498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497498]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08391_not_prime : ¬(recordGapCenter + 497732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497732]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08392_not_prime : ¬(recordGapCenter + 497738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497738]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08393_not_prime : ¬(recordGapCenter + 497786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497786]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08394_not_prime : ¬(recordGapCenter + 497870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 497870]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08395_not_prime : ¬(recordGapCenter + 498036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498036]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08396_not_prime : ¬(recordGapCenter + 498282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498282]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08397_not_prime : ¬(recordGapCenter + 498398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498398]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08398_not_prime : ¬(recordGapCenter + 498558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498558]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08399_not_prime : ¬(recordGapCenter + 498572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498572]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08400_not_prime : ¬(recordGapCenter + 498702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498702]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08401_not_prime : ¬(recordGapCenter + 498716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498716]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08402_not_prime : ¬(recordGapCenter + 498776).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498776]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08403_not_prime : ¬(recordGapCenter + 498842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498842]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08404_not_prime : ¬(recordGapCenter + 498878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 498878]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08405_not_prime : ¬(recordGapCenter + 499178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499178]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08406_not_prime : ¬(recordGapCenter + 499370).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499370]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08407_not_prime : ¬(recordGapCenter + 499412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499412]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08408_not_prime : ¬(recordGapCenter + 499430).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499430]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08409_not_prime : ¬(recordGapCenter + 499542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499542]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08410_not_prime : ¬(recordGapCenter + 499602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499602]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08411_not_prime : ¬(recordGapCenter + 499676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499676]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08412_not_prime : ¬(recordGapCenter + 499706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499706]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08413_not_prime : ¬(recordGapCenter + 499866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499866]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08414_not_prime : ¬(recordGapCenter + 499886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499886]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08415_not_prime : ¬(recordGapCenter + 499916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499916]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08416_not_prime : ¬(recordGapCenter + 499976).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 499976]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08417_not_prime : ¬(recordGapCenter + 500246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500246]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08418_not_prime : ¬(recordGapCenter + 500252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500252]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08419_not_prime : ¬(recordGapCenter + 500312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500312]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08420_not_prime : ¬(recordGapCenter + 500330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500330]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08421_not_prime : ¬(recordGapCenter + 500372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500372]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08422_not_prime : ¬(recordGapCenter + 500406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500406]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08423_not_prime : ¬(recordGapCenter + 500468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500468]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08424_not_prime : ¬(recordGapCenter + 500510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500510]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08425_not_prime : ¬(recordGapCenter + 500622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500622]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08426_not_prime : ¬(recordGapCenter + 500690).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500690]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08427_not_prime : ¬(recordGapCenter + 500876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500876]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08428_not_prime : ¬(recordGapCenter + 500882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500882]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08429_not_prime : ¬(recordGapCenter + 500978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 500978]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08430_not_prime : ¬(recordGapCenter + 501086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501086]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08431_not_prime : ¬(recordGapCenter + 501110).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501110]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08432_not_prime : ¬(recordGapCenter + 501362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501362]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08433_not_prime : ¬(recordGapCenter + 501506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501506]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08434_not_prime : ¬(recordGapCenter + 501548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501548]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08435_not_prime : ¬(recordGapCenter + 501590).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501590]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08436_not_prime : ¬(recordGapCenter + 501692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501692]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08437_not_prime : ¬(recordGapCenter + 501702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501702]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08438_not_prime : ¬(recordGapCenter + 501716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501716]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08439_not_prime : ¬(recordGapCenter + 501770).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501770]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08440_not_prime : ¬(recordGapCenter + 501848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501848]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08441_not_prime : ¬(recordGapCenter + 501918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501918]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08442_not_prime : ¬(recordGapCenter + 501938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501938]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08443_not_prime : ¬(recordGapCenter + 501986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 501986]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08444_not_prime : ¬(recordGapCenter + 502070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502070]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08445_not_prime : ¬(recordGapCenter + 502118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502118]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08446_not_prime : ¬(recordGapCenter + 502310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502310]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08447_not_prime : ¬(recordGapCenter + 502406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502406]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

theorem fullRecordGapTerm08448_not_prime : ¬(recordGapCenter + 502526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502526]
  · apply fullRecordGapRow00033_fermat
    simp [fullRecordGapRow00033_values]

end PrimeFactorUnimodality
