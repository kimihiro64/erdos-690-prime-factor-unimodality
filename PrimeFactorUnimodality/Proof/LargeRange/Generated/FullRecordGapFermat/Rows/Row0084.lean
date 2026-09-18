import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00084_values : List Nat :=
  [fullRecordGapCenterValue + 257666,
    fullRecordGapCenterValue + 257918,
    fullRecordGapCenterValue + 258002,
    fullRecordGapCenterValue + 258338,
    fullRecordGapCenterValue + 258578,
    fullRecordGapCenterValue + 258668,
    fullRecordGapCenterValue + 258798,
    fullRecordGapCenterValue + 258806,
    fullRecordGapCenterValue + 258878,
    fullRecordGapCenterValue + 259058,
    fullRecordGapCenterValue + 259106,
    fullRecordGapCenterValue + 259206,
    fullRecordGapCenterValue + 259268,
    fullRecordGapCenterValue + 259308,
    fullRecordGapCenterValue + 259466,
    fullRecordGapCenterValue + 259626,
    fullRecordGapCenterValue + 259682,
    fullRecordGapCenterValue + 259746,
    fullRecordGapCenterValue + 259802,
    fullRecordGapCenterValue + 259878,
    fullRecordGapCenterValue + 260006,
    fullRecordGapCenterValue + 260012,
    fullRecordGapCenterValue + 260198,
    fullRecordGapCenterValue + 260342,
    fullRecordGapCenterValue + 260492,
    fullRecordGapCenterValue + 260522,
    fullRecordGapCenterValue + 260558,
    fullRecordGapCenterValue + 260562,
    fullRecordGapCenterValue + 260726,
    fullRecordGapCenterValue + 260732,
    fullRecordGapCenterValue + 260738,
    fullRecordGapCenterValue + 260822,
    fullRecordGapCenterValue + 260846,
    fullRecordGapCenterValue + 260922,
    fullRecordGapCenterValue + 260978,
    fullRecordGapCenterValue + 261068,
    fullRecordGapCenterValue + 261236,
    fullRecordGapCenterValue + 261258,
    fullRecordGapCenterValue + 261278,
    fullRecordGapCenterValue + 261308,
    fullRecordGapCenterValue + 261362,
    fullRecordGapCenterValue + 261398,
    fullRecordGapCenterValue + 261788,
    fullRecordGapCenterValue + 261798,
    fullRecordGapCenterValue + 261938,
    fullRecordGapCenterValue + 261962,
    fullRecordGapCenterValue + 262118,
    fullRecordGapCenterValue + 262172,
    fullRecordGapCenterValue + 262406,
    fullRecordGapCenterValue + 262440,
    fullRecordGapCenterValue + 262442,
    fullRecordGapCenterValue + 262502,
    fullRecordGapCenterValue + 262532,
    fullRecordGapCenterValue + 262622,
    fullRecordGapCenterValue + 262628,
    fullRecordGapCenterValue + 262686,
    fullRecordGapCenterValue + 262826,
    fullRecordGapCenterValue + 262862,
    fullRecordGapCenterValue + 262868,
    fullRecordGapCenterValue + 262958,
    fullRecordGapCenterValue + 263342,
    fullRecordGapCenterValue + 263462,
    fullRecordGapCenterValue + 263478,
    fullRecordGapCenterValue + 263706]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00084_fermat : ∀ n ∈ fullRecordGapRow00084_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05313_not_prime : ¬(recordGapCenter + 257666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 257666]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05314_not_prime : ¬(recordGapCenter + 257918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 257918]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05315_not_prime : ¬(recordGapCenter + 258002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 258002]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05316_not_prime : ¬(recordGapCenter + 258338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 258338]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05317_not_prime : ¬(recordGapCenter + 258578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 258578]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05318_not_prime : ¬(recordGapCenter + 258668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 258668]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05319_not_prime : ¬(recordGapCenter + 258798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 258798]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05320_not_prime : ¬(recordGapCenter + 258806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 258806]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05321_not_prime : ¬(recordGapCenter + 258878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 258878]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05322_not_prime : ¬(recordGapCenter + 259058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 259058]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05323_not_prime : ¬(recordGapCenter + 259106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 259106]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05324_not_prime : ¬(recordGapCenter + 259206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 259206]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05325_not_prime : ¬(recordGapCenter + 259268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 259268]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05326_not_prime : ¬(recordGapCenter + 259308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 259308]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05327_not_prime : ¬(recordGapCenter + 259466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 259466]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05328_not_prime : ¬(recordGapCenter + 259626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 259626]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05329_not_prime : ¬(recordGapCenter + 259682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 259682]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05330_not_prime : ¬(recordGapCenter + 259746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 259746]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05331_not_prime : ¬(recordGapCenter + 259802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 259802]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05332_not_prime : ¬(recordGapCenter + 259878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 259878]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05333_not_prime : ¬(recordGapCenter + 260006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260006]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05334_not_prime : ¬(recordGapCenter + 260012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260012]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05335_not_prime : ¬(recordGapCenter + 260198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260198]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05336_not_prime : ¬(recordGapCenter + 260342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260342]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05337_not_prime : ¬(recordGapCenter + 260492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260492]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05338_not_prime : ¬(recordGapCenter + 260522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260522]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05339_not_prime : ¬(recordGapCenter + 260558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260558]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05340_not_prime : ¬(recordGapCenter + 260562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260562]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05341_not_prime : ¬(recordGapCenter + 260726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260726]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05342_not_prime : ¬(recordGapCenter + 260732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260732]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05343_not_prime : ¬(recordGapCenter + 260738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260738]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05344_not_prime : ¬(recordGapCenter + 260822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260822]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05345_not_prime : ¬(recordGapCenter + 260846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260846]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05346_not_prime : ¬(recordGapCenter + 260922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260922]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05347_not_prime : ¬(recordGapCenter + 260978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 260978]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05348_not_prime : ¬(recordGapCenter + 261068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 261068]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05349_not_prime : ¬(recordGapCenter + 261236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 261236]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05350_not_prime : ¬(recordGapCenter + 261258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 261258]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05351_not_prime : ¬(recordGapCenter + 261278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 261278]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05352_not_prime : ¬(recordGapCenter + 261308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 261308]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05353_not_prime : ¬(recordGapCenter + 261362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 261362]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05354_not_prime : ¬(recordGapCenter + 261398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 261398]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05355_not_prime : ¬(recordGapCenter + 261788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 261788]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05356_not_prime : ¬(recordGapCenter + 261798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 261798]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05357_not_prime : ¬(recordGapCenter + 261938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 261938]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05358_not_prime : ¬(recordGapCenter + 261962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 261962]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05359_not_prime : ¬(recordGapCenter + 262118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 262118]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05360_not_prime : ¬(recordGapCenter + 262172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 262172]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05361_not_prime : ¬(recordGapCenter + 262406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 262406]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05362_not_prime : ¬(recordGapCenter + 262440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 262440]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05363_not_prime : ¬(recordGapCenter + 262442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 262442]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05364_not_prime : ¬(recordGapCenter + 262502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 262502]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05365_not_prime : ¬(recordGapCenter + 262532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 262532]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05366_not_prime : ¬(recordGapCenter + 262622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 262622]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05367_not_prime : ¬(recordGapCenter + 262628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 262628]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05368_not_prime : ¬(recordGapCenter + 262686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 262686]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05369_not_prime : ¬(recordGapCenter + 262826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 262826]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05370_not_prime : ¬(recordGapCenter + 262862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 262862]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05371_not_prime : ¬(recordGapCenter + 262868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 262868]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05372_not_prime : ¬(recordGapCenter + 262958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 262958]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05373_not_prime : ¬(recordGapCenter + 263342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 263342]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05374_not_prime : ¬(recordGapCenter + 263462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 263462]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05375_not_prime : ¬(recordGapCenter + 263478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 263478]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

theorem fullRecordGapTerm05376_not_prime : ¬(recordGapCenter + 263706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 263706]
  · apply fullRecordGapRow00084_fermat
    simp [fullRecordGapRow00084_values]

end PrimeFactorUnimodality
