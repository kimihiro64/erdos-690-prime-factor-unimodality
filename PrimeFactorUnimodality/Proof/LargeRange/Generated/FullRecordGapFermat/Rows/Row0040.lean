import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00040_values : List Nat :=
  [fullRecordGapCenterValue - 245332,
    fullRecordGapCenterValue - 245188,
    fullRecordGapCenterValue - 244978,
    fullRecordGapCenterValue - 244944,
    fullRecordGapCenterValue - 244564,
    fullRecordGapCenterValue - 244558,
    fullRecordGapCenterValue - 244414,
    fullRecordGapCenterValue - 244234,
    fullRecordGapCenterValue - 244198,
    fullRecordGapCenterValue - 244102,
    fullRecordGapCenterValue - 244054,
    fullRecordGapCenterValue - 243778,
    fullRecordGapCenterValue - 243772,
    fullRecordGapCenterValue - 243604,
    fullRecordGapCenterValue - 243262,
    fullRecordGapCenterValue - 243172,
    fullRecordGapCenterValue - 243154,
    fullRecordGapCenterValue - 242938,
    fullRecordGapCenterValue - 242878,
    fullRecordGapCenterValue - 242842,
    fullRecordGapCenterValue - 242758,
    fullRecordGapCenterValue - 242644,
    fullRecordGapCenterValue - 242524,
    fullRecordGapCenterValue - 242458,
    fullRecordGapCenterValue - 242314,
    fullRecordGapCenterValue - 242134,
    fullRecordGapCenterValue - 242002,
    fullRecordGapCenterValue - 241920,
    fullRecordGapCenterValue - 241882,
    fullRecordGapCenterValue - 241372,
    fullRecordGapCenterValue - 241342,
    fullRecordGapCenterValue - 241294,
    fullRecordGapCenterValue - 240742,
    fullRecordGapCenterValue - 240532,
    fullRecordGapCenterValue - 240418,
    fullRecordGapCenterValue - 240412,
    fullRecordGapCenterValue - 240148,
    fullRecordGapCenterValue - 240100,
    fullRecordGapCenterValue - 240022,
    fullRecordGapCenterValue - 240000,
    fullRecordGapCenterValue - 239662,
    fullRecordGapCenterValue - 239332,
    fullRecordGapCenterValue - 239182,
    fullRecordGapCenterValue - 239164,
    fullRecordGapCenterValue - 239098,
    fullRecordGapCenterValue - 238978,
    fullRecordGapCenterValue - 238894,
    fullRecordGapCenterValue - 238828,
    fullRecordGapCenterValue - 238324,
    fullRecordGapCenterValue - 238318,
    fullRecordGapCenterValue - 237862,
    fullRecordGapCenterValue - 237814,
    fullRecordGapCenterValue - 237514,
    fullRecordGapCenterValue - 237502,
    fullRecordGapCenterValue - 237382,
    fullRecordGapCenterValue - 237160,
    fullRecordGapCenterValue - 237052,
    fullRecordGapCenterValue - 236932,
    fullRecordGapCenterValue - 236554,
    fullRecordGapCenterValue - 236544,
    fullRecordGapCenterValue - 236338,
    fullRecordGapCenterValue - 236332,
    fullRecordGapCenterValue - 236250,
    fullRecordGapCenterValue - 236212]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00040_fermat : ∀ n ∈ fullRecordGapRow00040_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02497_not_prime : ¬(recordGapCenter - 245332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245332]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02498_not_prime : ¬(recordGapCenter - 245188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245188]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02499_not_prime : ¬(recordGapCenter - 244978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244978]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02500_not_prime : ¬(recordGapCenter - 244944).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244944]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02501_not_prime : ¬(recordGapCenter - 244564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244564]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02502_not_prime : ¬(recordGapCenter - 244558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244558]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02503_not_prime : ¬(recordGapCenter - 244414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244414]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02504_not_prime : ¬(recordGapCenter - 244234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244234]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02505_not_prime : ¬(recordGapCenter - 244198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244198]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02506_not_prime : ¬(recordGapCenter - 244102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244102]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02507_not_prime : ¬(recordGapCenter - 244054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244054]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02508_not_prime : ¬(recordGapCenter - 243778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 243778]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02509_not_prime : ¬(recordGapCenter - 243772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 243772]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02510_not_prime : ¬(recordGapCenter - 243604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 243604]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02511_not_prime : ¬(recordGapCenter - 243262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 243262]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02512_not_prime : ¬(recordGapCenter - 243172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 243172]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02513_not_prime : ¬(recordGapCenter - 243154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 243154]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02514_not_prime : ¬(recordGapCenter - 242938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242938]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02515_not_prime : ¬(recordGapCenter - 242878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242878]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02516_not_prime : ¬(recordGapCenter - 242842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242842]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02517_not_prime : ¬(recordGapCenter - 242758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242758]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02518_not_prime : ¬(recordGapCenter - 242644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242644]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02519_not_prime : ¬(recordGapCenter - 242524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242524]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02520_not_prime : ¬(recordGapCenter - 242458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242458]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02521_not_prime : ¬(recordGapCenter - 242314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242314]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02522_not_prime : ¬(recordGapCenter - 242134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242134]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02523_not_prime : ¬(recordGapCenter - 242002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242002]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02524_not_prime : ¬(recordGapCenter - 241920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 241920]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02525_not_prime : ¬(recordGapCenter - 241882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 241882]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02526_not_prime : ¬(recordGapCenter - 241372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 241372]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02527_not_prime : ¬(recordGapCenter - 241342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 241342]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02528_not_prime : ¬(recordGapCenter - 241294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 241294]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02529_not_prime : ¬(recordGapCenter - 240742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240742]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02530_not_prime : ¬(recordGapCenter - 240532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240532]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02531_not_prime : ¬(recordGapCenter - 240418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240418]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02532_not_prime : ¬(recordGapCenter - 240412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240412]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02533_not_prime : ¬(recordGapCenter - 240148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240148]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02534_not_prime : ¬(recordGapCenter - 240100).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240100]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02535_not_prime : ¬(recordGapCenter - 240022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240022]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02536_not_prime : ¬(recordGapCenter - 240000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240000]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02537_not_prime : ¬(recordGapCenter - 239662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 239662]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02538_not_prime : ¬(recordGapCenter - 239332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 239332]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02539_not_prime : ¬(recordGapCenter - 239182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 239182]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02540_not_prime : ¬(recordGapCenter - 239164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 239164]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02541_not_prime : ¬(recordGapCenter - 239098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 239098]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02542_not_prime : ¬(recordGapCenter - 238978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 238978]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02543_not_prime : ¬(recordGapCenter - 238894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 238894]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02544_not_prime : ¬(recordGapCenter - 238828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 238828]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02545_not_prime : ¬(recordGapCenter - 238324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 238324]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02546_not_prime : ¬(recordGapCenter - 238318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 238318]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02547_not_prime : ¬(recordGapCenter - 237862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 237862]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02548_not_prime : ¬(recordGapCenter - 237814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 237814]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02549_not_prime : ¬(recordGapCenter - 237514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 237514]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02550_not_prime : ¬(recordGapCenter - 237502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 237502]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02551_not_prime : ¬(recordGapCenter - 237382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 237382]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02552_not_prime : ¬(recordGapCenter - 237160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 237160]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02553_not_prime : ¬(recordGapCenter - 237052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 237052]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02554_not_prime : ¬(recordGapCenter - 236932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236932]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02555_not_prime : ¬(recordGapCenter - 236554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236554]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02556_not_prime : ¬(recordGapCenter - 236544).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236544]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02557_not_prime : ¬(recordGapCenter - 236338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236338]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02558_not_prime : ¬(recordGapCenter - 236332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236332]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02559_not_prime : ¬(recordGapCenter - 236250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236250]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

theorem fullRecordGapTerm02560_not_prime : ¬(recordGapCenter - 236212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236212]
  · apply fullRecordGapRow00040_fermat
    simp [fullRecordGapRow00040_values]

end PrimeFactorUnimodality
