import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00087_values : List Nat :=
  [fullRecordGapCenterValue + 274982,
    fullRecordGapCenterValue + 275108,
    fullRecordGapCenterValue + 275186,
    fullRecordGapCenterValue + 275318,
    fullRecordGapCenterValue + 275426,
    fullRecordGapCenterValue + 275516,
    fullRecordGapCenterValue + 275562,
    fullRecordGapCenterValue + 275588,
    fullRecordGapCenterValue + 275636,
    fullRecordGapCenterValue + 275658,
    fullRecordGapCenterValue + 275718,
    fullRecordGapCenterValue + 275738,
    fullRecordGapCenterValue + 275822,
    fullRecordGapCenterValue + 275852,
    fullRecordGapCenterValue + 275882,
    fullRecordGapCenterValue + 275966,
    fullRecordGapCenterValue + 276126,
    fullRecordGapCenterValue + 276158,
    fullRecordGapCenterValue + 276362,
    fullRecordGapCenterValue + 276578,
    fullRecordGapCenterValue + 276698,
    fullRecordGapCenterValue + 276846,
    fullRecordGapCenterValue + 276882,
    fullRecordGapCenterValue + 276902,
    fullRecordGapCenterValue + 277118,
    fullRecordGapCenterValue + 277268,
    fullRecordGapCenterValue + 277422,
    fullRecordGapCenterValue + 277586,
    fullRecordGapCenterValue + 277778,
    fullRecordGapCenterValue + 277806,
    fullRecordGapCenterValue + 277830,
    fullRecordGapCenterValue + 277868,
    fullRecordGapCenterValue + 278246,
    fullRecordGapCenterValue + 278612,
    fullRecordGapCenterValue + 278618,
    fullRecordGapCenterValue + 278666,
    fullRecordGapCenterValue + 278678,
    fullRecordGapCenterValue + 278682,
    fullRecordGapCenterValue + 278708,
    fullRecordGapCenterValue + 278742,
    fullRecordGapCenterValue + 278826,
    fullRecordGapCenterValue + 278948,
    fullRecordGapCenterValue + 279218,
    fullRecordGapCenterValue + 279332,
    fullRecordGapCenterValue + 279438,
    fullRecordGapCenterValue + 279458,
    fullRecordGapCenterValue + 279510,
    fullRecordGapCenterValue + 279546,
    fullRecordGapCenterValue + 279596,
    fullRecordGapCenterValue + 279606,
    fullRecordGapCenterValue + 279662,
    fullRecordGapCenterValue + 279798,
    fullRecordGapCenterValue + 279878,
    fullRecordGapCenterValue + 279998,
    fullRecordGapCenterValue + 280106,
    fullRecordGapCenterValue + 280142,
    fullRecordGapCenterValue + 280218,
    fullRecordGapCenterValue + 280382,
    fullRecordGapCenterValue + 280506,
    fullRecordGapCenterValue + 280556,
    fullRecordGapCenterValue + 280838,
    fullRecordGapCenterValue + 280842,
    fullRecordGapCenterValue + 280886,
    fullRecordGapCenterValue + 280898]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00087_fermat : ∀ n ∈ fullRecordGapRow00087_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05505_not_prime : ¬(recordGapCenter + 274982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 274982]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05506_not_prime : ¬(recordGapCenter + 275108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275108]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05507_not_prime : ¬(recordGapCenter + 275186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275186]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05508_not_prime : ¬(recordGapCenter + 275318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275318]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05509_not_prime : ¬(recordGapCenter + 275426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275426]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05510_not_prime : ¬(recordGapCenter + 275516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275516]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05511_not_prime : ¬(recordGapCenter + 275562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275562]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05512_not_prime : ¬(recordGapCenter + 275588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275588]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05513_not_prime : ¬(recordGapCenter + 275636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275636]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05514_not_prime : ¬(recordGapCenter + 275658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275658]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05515_not_prime : ¬(recordGapCenter + 275718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275718]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05516_not_prime : ¬(recordGapCenter + 275738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275738]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05517_not_prime : ¬(recordGapCenter + 275822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275822]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05518_not_prime : ¬(recordGapCenter + 275852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275852]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05519_not_prime : ¬(recordGapCenter + 275882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275882]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05520_not_prime : ¬(recordGapCenter + 275966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 275966]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05521_not_prime : ¬(recordGapCenter + 276126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 276126]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05522_not_prime : ¬(recordGapCenter + 276158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 276158]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05523_not_prime : ¬(recordGapCenter + 276362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 276362]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05524_not_prime : ¬(recordGapCenter + 276578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 276578]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05525_not_prime : ¬(recordGapCenter + 276698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 276698]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05526_not_prime : ¬(recordGapCenter + 276846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 276846]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05527_not_prime : ¬(recordGapCenter + 276882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 276882]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05528_not_prime : ¬(recordGapCenter + 276902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 276902]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05529_not_prime : ¬(recordGapCenter + 277118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 277118]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05530_not_prime : ¬(recordGapCenter + 277268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 277268]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05531_not_prime : ¬(recordGapCenter + 277422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 277422]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05532_not_prime : ¬(recordGapCenter + 277586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 277586]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05533_not_prime : ¬(recordGapCenter + 277778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 277778]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05534_not_prime : ¬(recordGapCenter + 277806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 277806]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05535_not_prime : ¬(recordGapCenter + 277830).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 277830]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05536_not_prime : ¬(recordGapCenter + 277868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 277868]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05537_not_prime : ¬(recordGapCenter + 278246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 278246]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05538_not_prime : ¬(recordGapCenter + 278612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 278612]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05539_not_prime : ¬(recordGapCenter + 278618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 278618]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05540_not_prime : ¬(recordGapCenter + 278666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 278666]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05541_not_prime : ¬(recordGapCenter + 278678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 278678]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05542_not_prime : ¬(recordGapCenter + 278682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 278682]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05543_not_prime : ¬(recordGapCenter + 278708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 278708]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05544_not_prime : ¬(recordGapCenter + 278742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 278742]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05545_not_prime : ¬(recordGapCenter + 278826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 278826]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05546_not_prime : ¬(recordGapCenter + 278948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 278948]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05547_not_prime : ¬(recordGapCenter + 279218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 279218]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05548_not_prime : ¬(recordGapCenter + 279332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 279332]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05549_not_prime : ¬(recordGapCenter + 279438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 279438]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05550_not_prime : ¬(recordGapCenter + 279458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 279458]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05551_not_prime : ¬(recordGapCenter + 279510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 279510]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05552_not_prime : ¬(recordGapCenter + 279546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 279546]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05553_not_prime : ¬(recordGapCenter + 279596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 279596]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05554_not_prime : ¬(recordGapCenter + 279606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 279606]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05555_not_prime : ¬(recordGapCenter + 279662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 279662]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05556_not_prime : ¬(recordGapCenter + 279798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 279798]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05557_not_prime : ¬(recordGapCenter + 279878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 279878]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05558_not_prime : ¬(recordGapCenter + 279998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 279998]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05559_not_prime : ¬(recordGapCenter + 280106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 280106]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05560_not_prime : ¬(recordGapCenter + 280142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 280142]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05561_not_prime : ¬(recordGapCenter + 280218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 280218]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05562_not_prime : ¬(recordGapCenter + 280382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 280382]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05563_not_prime : ¬(recordGapCenter + 280506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 280506]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05564_not_prime : ¬(recordGapCenter + 280556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 280556]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05565_not_prime : ¬(recordGapCenter + 280838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 280838]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05566_not_prime : ¬(recordGapCenter + 280842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 280842]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05567_not_prime : ¬(recordGapCenter + 280886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 280886]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

theorem fullRecordGapTerm05568_not_prime : ¬(recordGapCenter + 280898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 280898]
  · apply fullRecordGapRow00087_fermat
    simp [fullRecordGapRow00087_values]

end PrimeFactorUnimodality
