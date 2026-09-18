import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00146_values : List Nat :=
  [fullRecordGapCenterValue + 556188,
    fullRecordGapCenterValue + 556190,
    fullRecordGapCenterValue + 556242,
    fullRecordGapCenterValue + 556298,
    fullRecordGapCenterValue + 556302,
    fullRecordGapCenterValue + 556382,
    fullRecordGapCenterValue + 556518,
    fullRecordGapCenterValue + 556532,
    fullRecordGapCenterValue + 556602,
    fullRecordGapCenterValue + 556610,
    fullRecordGapCenterValue + 556658,
    fullRecordGapCenterValue + 556676,
    fullRecordGapCenterValue + 556748,
    fullRecordGapCenterValue + 556788,
    fullRecordGapCenterValue + 556826,
    fullRecordGapCenterValue + 556932,
    fullRecordGapCenterValue + 556958,
    fullRecordGapCenterValue + 557202,
    fullRecordGapCenterValue + 557222,
    fullRecordGapCenterValue + 557246,
    fullRecordGapCenterValue + 557252,
    fullRecordGapCenterValue + 557288,
    fullRecordGapCenterValue + 557330,
    fullRecordGapCenterValue + 557342,
    fullRecordGapCenterValue + 557358,
    fullRecordGapCenterValue + 557378,
    fullRecordGapCenterValue + 557412,
    fullRecordGapCenterValue + 557468,
    fullRecordGapCenterValue + 557588,
    fullRecordGapCenterValue + 557618,
    fullRecordGapCenterValue + 557636,
    fullRecordGapCenterValue + 557742,
    fullRecordGapCenterValue + 557756,
    fullRecordGapCenterValue + 557922,
    fullRecordGapCenterValue + 557958,
    fullRecordGapCenterValue + 558188,
    fullRecordGapCenterValue + 558276,
    fullRecordGapCenterValue + 558318,
    fullRecordGapCenterValue + 558498,
    fullRecordGapCenterValue + 558588,
    fullRecordGapCenterValue + 558632,
    fullRecordGapCenterValue + 558678,
    fullRecordGapCenterValue + 558710,
    fullRecordGapCenterValue + 558786,
    fullRecordGapCenterValue + 558798,
    fullRecordGapCenterValue + 558842,
    fullRecordGapCenterValue + 558890,
    fullRecordGapCenterValue + 558902,
    fullRecordGapCenterValue + 558962,
    fullRecordGapCenterValue + 559046,
    fullRecordGapCenterValue + 559142,
    fullRecordGapCenterValue + 559226,
    fullRecordGapCenterValue + 559238,
    fullRecordGapCenterValue + 559298,
    fullRecordGapCenterValue + 559428,
    fullRecordGapCenterValue + 559448,
    fullRecordGapCenterValue + 559542,
    fullRecordGapCenterValue + 559578,
    fullRecordGapCenterValue + 559596,
    fullRecordGapCenterValue + 559766,
    fullRecordGapCenterValue + 559826,
    fullRecordGapCenterValue + 559868,
    fullRecordGapCenterValue + 559898,
    fullRecordGapCenterValue + 559938]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00146_fermat : ∀ n ∈ fullRecordGapRow00146_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09281_not_prime : ¬(recordGapCenter + 556188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556188]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09282_not_prime : ¬(recordGapCenter + 556190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556190]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09283_not_prime : ¬(recordGapCenter + 556242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556242]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09284_not_prime : ¬(recordGapCenter + 556298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556298]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09285_not_prime : ¬(recordGapCenter + 556302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556302]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09286_not_prime : ¬(recordGapCenter + 556382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556382]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09287_not_prime : ¬(recordGapCenter + 556518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556518]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09288_not_prime : ¬(recordGapCenter + 556532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556532]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09289_not_prime : ¬(recordGapCenter + 556602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556602]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09290_not_prime : ¬(recordGapCenter + 556610).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556610]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09291_not_prime : ¬(recordGapCenter + 556658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556658]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09292_not_prime : ¬(recordGapCenter + 556676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556676]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09293_not_prime : ¬(recordGapCenter + 556748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556748]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09294_not_prime : ¬(recordGapCenter + 556788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556788]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09295_not_prime : ¬(recordGapCenter + 556826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556826]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09296_not_prime : ¬(recordGapCenter + 556932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556932]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09297_not_prime : ¬(recordGapCenter + 556958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 556958]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09298_not_prime : ¬(recordGapCenter + 557202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557202]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09299_not_prime : ¬(recordGapCenter + 557222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557222]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09300_not_prime : ¬(recordGapCenter + 557246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557246]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09301_not_prime : ¬(recordGapCenter + 557252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557252]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09302_not_prime : ¬(recordGapCenter + 557288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557288]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09303_not_prime : ¬(recordGapCenter + 557330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557330]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09304_not_prime : ¬(recordGapCenter + 557342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557342]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09305_not_prime : ¬(recordGapCenter + 557358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557358]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09306_not_prime : ¬(recordGapCenter + 557378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557378]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09307_not_prime : ¬(recordGapCenter + 557412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557412]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09308_not_prime : ¬(recordGapCenter + 557468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557468]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09309_not_prime : ¬(recordGapCenter + 557588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557588]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09310_not_prime : ¬(recordGapCenter + 557618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557618]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09311_not_prime : ¬(recordGapCenter + 557636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557636]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09312_not_prime : ¬(recordGapCenter + 557742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557742]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09313_not_prime : ¬(recordGapCenter + 557756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557756]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09314_not_prime : ¬(recordGapCenter + 557922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557922]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09315_not_prime : ¬(recordGapCenter + 557958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 557958]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09316_not_prime : ¬(recordGapCenter + 558188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 558188]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09317_not_prime : ¬(recordGapCenter + 558276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 558276]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09318_not_prime : ¬(recordGapCenter + 558318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 558318]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09319_not_prime : ¬(recordGapCenter + 558498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 558498]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09320_not_prime : ¬(recordGapCenter + 558588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 558588]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09321_not_prime : ¬(recordGapCenter + 558632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 558632]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09322_not_prime : ¬(recordGapCenter + 558678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 558678]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09323_not_prime : ¬(recordGapCenter + 558710).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 558710]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09324_not_prime : ¬(recordGapCenter + 558786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 558786]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09325_not_prime : ¬(recordGapCenter + 558798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 558798]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09326_not_prime : ¬(recordGapCenter + 558842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 558842]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09327_not_prime : ¬(recordGapCenter + 558890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 558890]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09328_not_prime : ¬(recordGapCenter + 558902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 558902]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09329_not_prime : ¬(recordGapCenter + 558962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 558962]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09330_not_prime : ¬(recordGapCenter + 559046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559046]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09331_not_prime : ¬(recordGapCenter + 559142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559142]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09332_not_prime : ¬(recordGapCenter + 559226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559226]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09333_not_prime : ¬(recordGapCenter + 559238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559238]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09334_not_prime : ¬(recordGapCenter + 559298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559298]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09335_not_prime : ¬(recordGapCenter + 559428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559428]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09336_not_prime : ¬(recordGapCenter + 559448).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559448]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09337_not_prime : ¬(recordGapCenter + 559542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559542]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09338_not_prime : ¬(recordGapCenter + 559578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559578]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09339_not_prime : ¬(recordGapCenter + 559596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559596]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09340_not_prime : ¬(recordGapCenter + 559766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559766]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09341_not_prime : ¬(recordGapCenter + 559826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559826]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09342_not_prime : ¬(recordGapCenter + 559868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559868]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09343_not_prime : ¬(recordGapCenter + 559898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559898]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

theorem fullRecordGapTerm09344_not_prime : ¬(recordGapCenter + 559938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559938]
  · apply fullRecordGapRow00146_fermat
    simp [fullRecordGapRow00146_values]

end PrimeFactorUnimodality
