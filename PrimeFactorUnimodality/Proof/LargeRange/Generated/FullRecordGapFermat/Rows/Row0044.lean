import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00044_values : List Nat :=
  [fullRecordGapCenterValue - 213274,
    fullRecordGapCenterValue - 213082,
    fullRecordGapCenterValue - 212974,
    fullRecordGapCenterValue - 212782,
    fullRecordGapCenterValue - 212698,
    fullRecordGapCenterValue - 212662,
    fullRecordGapCenterValue - 212434,
    fullRecordGapCenterValue - 212404,
    fullRecordGapCenterValue - 212242,
    fullRecordGapCenterValue - 212218,
    fullRecordGapCenterValue - 211942,
    fullRecordGapCenterValue - 211852,
    fullRecordGapCenterValue - 211804,
    fullRecordGapCenterValue - 211750,
    fullRecordGapCenterValue - 211680,
    fullRecordGapCenterValue - 211612,
    fullRecordGapCenterValue - 211348,
    fullRecordGapCenterValue - 211054,
    fullRecordGapCenterValue - 210814,
    fullRecordGapCenterValue - 210802,
    fullRecordGapCenterValue - 210718,
    fullRecordGapCenterValue - 210682,
    fullRecordGapCenterValue - 210502,
    fullRecordGapCenterValue - 210244,
    fullRecordGapCenterValue - 210142,
    fullRecordGapCenterValue - 210004,
    fullRecordGapCenterValue - 209758,
    fullRecordGapCenterValue - 209548,
    fullRecordGapCenterValue - 209452,
    fullRecordGapCenterValue - 209122,
    fullRecordGapCenterValue - 209088,
    fullRecordGapCenterValue - 208918,
    fullRecordGapCenterValue - 208834,
    fullRecordGapCenterValue - 208738,
    fullRecordGapCenterValue - 208708,
    fullRecordGapCenterValue - 208612,
    fullRecordGapCenterValue - 208414,
    fullRecordGapCenterValue - 208324,
    fullRecordGapCenterValue - 208228,
    fullRecordGapCenterValue - 208204,
    fullRecordGapCenterValue - 208084,
    fullRecordGapCenterValue - 208018,
    fullRecordGapCenterValue - 207982,
    fullRecordGapCenterValue - 207934,
    fullRecordGapCenterValue - 207900,
    fullRecordGapCenterValue - 207682,
    fullRecordGapCenterValue - 207652,
    fullRecordGapCenterValue - 207412,
    fullRecordGapCenterValue - 207268,
    fullRecordGapCenterValue - 207238,
    fullRecordGapCenterValue - 207058,
    fullRecordGapCenterValue - 206902,
    fullRecordGapCenterValue - 206842,
    fullRecordGapCenterValue - 206818,
    fullRecordGapCenterValue - 206698,
    fullRecordGapCenterValue - 206638,
    fullRecordGapCenterValue - 206614,
    fullRecordGapCenterValue - 206308,
    fullRecordGapCenterValue - 206250,
    fullRecordGapCenterValue - 206098,
    fullRecordGapCenterValue - 206068,
    fullRecordGapCenterValue - 206014,
    fullRecordGapCenterValue - 205522,
    fullRecordGapCenterValue - 205228]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00044_fermat : ∀ n ∈ fullRecordGapRow00044_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02753_not_prime : ¬(recordGapCenter - 213274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213274]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02754_not_prime : ¬(recordGapCenter - 213082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213082]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02755_not_prime : ¬(recordGapCenter - 212974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212974]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02756_not_prime : ¬(recordGapCenter - 212782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212782]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02757_not_prime : ¬(recordGapCenter - 212698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212698]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02758_not_prime : ¬(recordGapCenter - 212662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212662]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02759_not_prime : ¬(recordGapCenter - 212434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212434]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02760_not_prime : ¬(recordGapCenter - 212404).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212404]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02761_not_prime : ¬(recordGapCenter - 212242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212242]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02762_not_prime : ¬(recordGapCenter - 212218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212218]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02763_not_prime : ¬(recordGapCenter - 211942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211942]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02764_not_prime : ¬(recordGapCenter - 211852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211852]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02765_not_prime : ¬(recordGapCenter - 211804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211804]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02766_not_prime : ¬(recordGapCenter - 211750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211750]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02767_not_prime : ¬(recordGapCenter - 211680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211680]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02768_not_prime : ¬(recordGapCenter - 211612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211612]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02769_not_prime : ¬(recordGapCenter - 211348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211348]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02770_not_prime : ¬(recordGapCenter - 211054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211054]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02771_not_prime : ¬(recordGapCenter - 210814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210814]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02772_not_prime : ¬(recordGapCenter - 210802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210802]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02773_not_prime : ¬(recordGapCenter - 210718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210718]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02774_not_prime : ¬(recordGapCenter - 210682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210682]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02775_not_prime : ¬(recordGapCenter - 210502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210502]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02776_not_prime : ¬(recordGapCenter - 210244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210244]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02777_not_prime : ¬(recordGapCenter - 210142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210142]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02778_not_prime : ¬(recordGapCenter - 210004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210004]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02779_not_prime : ¬(recordGapCenter - 209758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 209758]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02780_not_prime : ¬(recordGapCenter - 209548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 209548]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02781_not_prime : ¬(recordGapCenter - 209452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 209452]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02782_not_prime : ¬(recordGapCenter - 209122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 209122]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02783_not_prime : ¬(recordGapCenter - 209088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 209088]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02784_not_prime : ¬(recordGapCenter - 208918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208918]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02785_not_prime : ¬(recordGapCenter - 208834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208834]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02786_not_prime : ¬(recordGapCenter - 208738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208738]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02787_not_prime : ¬(recordGapCenter - 208708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208708]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02788_not_prime : ¬(recordGapCenter - 208612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208612]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02789_not_prime : ¬(recordGapCenter - 208414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208414]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02790_not_prime : ¬(recordGapCenter - 208324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208324]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02791_not_prime : ¬(recordGapCenter - 208228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208228]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02792_not_prime : ¬(recordGapCenter - 208204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208204]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02793_not_prime : ¬(recordGapCenter - 208084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208084]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02794_not_prime : ¬(recordGapCenter - 208018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208018]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02795_not_prime : ¬(recordGapCenter - 207982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207982]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02796_not_prime : ¬(recordGapCenter - 207934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207934]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02797_not_prime : ¬(recordGapCenter - 207900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207900]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02798_not_prime : ¬(recordGapCenter - 207682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207682]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02799_not_prime : ¬(recordGapCenter - 207652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207652]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02800_not_prime : ¬(recordGapCenter - 207412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207412]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02801_not_prime : ¬(recordGapCenter - 207268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207268]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02802_not_prime : ¬(recordGapCenter - 207238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207238]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02803_not_prime : ¬(recordGapCenter - 207058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207058]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02804_not_prime : ¬(recordGapCenter - 206902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206902]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02805_not_prime : ¬(recordGapCenter - 206842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206842]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02806_not_prime : ¬(recordGapCenter - 206818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206818]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02807_not_prime : ¬(recordGapCenter - 206698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206698]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02808_not_prime : ¬(recordGapCenter - 206638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206638]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02809_not_prime : ¬(recordGapCenter - 206614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206614]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02810_not_prime : ¬(recordGapCenter - 206308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206308]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02811_not_prime : ¬(recordGapCenter - 206250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206250]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02812_not_prime : ¬(recordGapCenter - 206098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206098]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02813_not_prime : ¬(recordGapCenter - 206068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206068]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02814_not_prime : ¬(recordGapCenter - 206014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206014]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02815_not_prime : ¬(recordGapCenter - 205522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 205522]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

theorem fullRecordGapTerm02816_not_prime : ¬(recordGapCenter - 205228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 205228]
  · apply fullRecordGapRow00044_fermat
    simp [fullRecordGapRow00044_values]

end PrimeFactorUnimodality
