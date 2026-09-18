import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00086_values : List Nat :=
  [fullRecordGapCenterValue + 269502,
    fullRecordGapCenterValue + 269708,
    fullRecordGapCenterValue + 269732,
    fullRecordGapCenterValue + 269778,
    fullRecordGapCenterValue + 269846,
    fullRecordGapCenterValue + 269922,
    fullRecordGapCenterValue + 269978,
    fullRecordGapCenterValue + 270042,
    fullRecordGapCenterValue + 270078,
    fullRecordGapCenterValue + 270086,
    fullRecordGapCenterValue + 270092,
    fullRecordGapCenterValue + 270302,
    fullRecordGapCenterValue + 270308,
    fullRecordGapCenterValue + 270356,
    fullRecordGapCenterValue + 270462,
    fullRecordGapCenterValue + 270498,
    fullRecordGapCenterValue + 270638,
    fullRecordGapCenterValue + 270698,
    fullRecordGapCenterValue + 270726,
    fullRecordGapCenterValue + 270786,
    fullRecordGapCenterValue + 270966,
    fullRecordGapCenterValue + 271022,
    fullRecordGapCenterValue + 271028,
    fullRecordGapCenterValue + 271040,
    fullRecordGapCenterValue + 271086,
    fullRecordGapCenterValue + 271118,
    fullRecordGapCenterValue + 271182,
    fullRecordGapCenterValue + 271202,
    fullRecordGapCenterValue + 271226,
    fullRecordGapCenterValue + 271482,
    fullRecordGapCenterValue + 271598,
    fullRecordGapCenterValue + 271656,
    fullRecordGapCenterValue + 271658,
    fullRecordGapCenterValue + 271826,
    fullRecordGapCenterValue + 272022,
    fullRecordGapCenterValue + 272046,
    fullRecordGapCenterValue + 272058,
    fullRecordGapCenterValue + 272160,
    fullRecordGapCenterValue + 272198,
    fullRecordGapCenterValue + 272478,
    fullRecordGapCenterValue + 272522,
    fullRecordGapCenterValue + 272562,
    fullRecordGapCenterValue + 272858,
    fullRecordGapCenterValue + 272946,
    fullRecordGapCenterValue + 272982,
    fullRecordGapCenterValue + 273002,
    fullRecordGapCenterValue + 273116,
    fullRecordGapCenterValue + 273198,
    fullRecordGapCenterValue + 273386,
    fullRecordGapCenterValue + 273506,
    fullRecordGapCenterValue + 273626,
    fullRecordGapCenterValue + 273758,
    fullRecordGapCenterValue + 273998,
    fullRecordGapCenterValue + 274002,
    fullRecordGapCenterValue + 274062,
    fullRecordGapCenterValue + 274382,
    fullRecordGapCenterValue + 274478,
    fullRecordGapCenterValue + 274502,
    fullRecordGapCenterValue + 274676,
    fullRecordGapCenterValue + 274682,
    fullRecordGapCenterValue + 274718,
    fullRecordGapCenterValue + 274766,
    fullRecordGapCenterValue + 274796,
    fullRecordGapCenterValue + 274916]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00086_fermat : ∀ n ∈ fullRecordGapRow00086_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05441_not_prime : ¬(recordGapCenter + 269502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 269502]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05442_not_prime : ¬(recordGapCenter + 269708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 269708]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05443_not_prime : ¬(recordGapCenter + 269732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 269732]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05444_not_prime : ¬(recordGapCenter + 269778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 269778]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05445_not_prime : ¬(recordGapCenter + 269846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 269846]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05446_not_prime : ¬(recordGapCenter + 269922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 269922]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05447_not_prime : ¬(recordGapCenter + 269978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 269978]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05448_not_prime : ¬(recordGapCenter + 270042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 270042]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05449_not_prime : ¬(recordGapCenter + 270078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 270078]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05450_not_prime : ¬(recordGapCenter + 270086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 270086]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05451_not_prime : ¬(recordGapCenter + 270092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 270092]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05452_not_prime : ¬(recordGapCenter + 270302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 270302]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05453_not_prime : ¬(recordGapCenter + 270308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 270308]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05454_not_prime : ¬(recordGapCenter + 270356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 270356]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05455_not_prime : ¬(recordGapCenter + 270462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 270462]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05456_not_prime : ¬(recordGapCenter + 270498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 270498]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05457_not_prime : ¬(recordGapCenter + 270638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 270638]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05458_not_prime : ¬(recordGapCenter + 270698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 270698]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05459_not_prime : ¬(recordGapCenter + 270726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 270726]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05460_not_prime : ¬(recordGapCenter + 270786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 270786]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05461_not_prime : ¬(recordGapCenter + 270966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 270966]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05462_not_prime : ¬(recordGapCenter + 271022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 271022]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05463_not_prime : ¬(recordGapCenter + 271028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 271028]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05464_not_prime : ¬(recordGapCenter + 271040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 271040]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05465_not_prime : ¬(recordGapCenter + 271086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 271086]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05466_not_prime : ¬(recordGapCenter + 271118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 271118]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05467_not_prime : ¬(recordGapCenter + 271182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 271182]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05468_not_prime : ¬(recordGapCenter + 271202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 271202]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05469_not_prime : ¬(recordGapCenter + 271226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 271226]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05470_not_prime : ¬(recordGapCenter + 271482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 271482]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05471_not_prime : ¬(recordGapCenter + 271598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 271598]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05472_not_prime : ¬(recordGapCenter + 271656).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 271656]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05473_not_prime : ¬(recordGapCenter + 271658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 271658]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05474_not_prime : ¬(recordGapCenter + 271826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 271826]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05475_not_prime : ¬(recordGapCenter + 272022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 272022]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05476_not_prime : ¬(recordGapCenter + 272046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 272046]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05477_not_prime : ¬(recordGapCenter + 272058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 272058]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05478_not_prime : ¬(recordGapCenter + 272160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 272160]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05479_not_prime : ¬(recordGapCenter + 272198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 272198]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05480_not_prime : ¬(recordGapCenter + 272478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 272478]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05481_not_prime : ¬(recordGapCenter + 272522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 272522]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05482_not_prime : ¬(recordGapCenter + 272562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 272562]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05483_not_prime : ¬(recordGapCenter + 272858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 272858]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05484_not_prime : ¬(recordGapCenter + 272946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 272946]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05485_not_prime : ¬(recordGapCenter + 272982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 272982]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05486_not_prime : ¬(recordGapCenter + 273002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 273002]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05487_not_prime : ¬(recordGapCenter + 273116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 273116]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05488_not_prime : ¬(recordGapCenter + 273198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 273198]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05489_not_prime : ¬(recordGapCenter + 273386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 273386]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05490_not_prime : ¬(recordGapCenter + 273506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 273506]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05491_not_prime : ¬(recordGapCenter + 273626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 273626]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05492_not_prime : ¬(recordGapCenter + 273758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 273758]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05493_not_prime : ¬(recordGapCenter + 273998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 273998]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05494_not_prime : ¬(recordGapCenter + 274002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 274002]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05495_not_prime : ¬(recordGapCenter + 274062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 274062]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05496_not_prime : ¬(recordGapCenter + 274382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 274382]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05497_not_prime : ¬(recordGapCenter + 274478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 274478]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05498_not_prime : ¬(recordGapCenter + 274502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 274502]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05499_not_prime : ¬(recordGapCenter + 274676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 274676]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05500_not_prime : ¬(recordGapCenter + 274682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 274682]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05501_not_prime : ¬(recordGapCenter + 274718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 274718]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05502_not_prime : ¬(recordGapCenter + 274766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 274766]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05503_not_prime : ¬(recordGapCenter + 274796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 274796]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

theorem fullRecordGapTerm05504_not_prime : ¬(recordGapCenter + 274916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 274916]
  · apply fullRecordGapRow00086_fermat
    simp [fullRecordGapRow00086_values]

end PrimeFactorUnimodality
