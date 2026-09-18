import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00170_values : List Nat :=
  [fullRecordGapCenterValue + 651786,
    fullRecordGapCenterValue + 651788,
    fullRecordGapCenterValue + 651842,
    fullRecordGapCenterValue + 651876,
    fullRecordGapCenterValue + 651956,
    fullRecordGapCenterValue + 651998,
    fullRecordGapCenterValue + 652022,
    fullRecordGapCenterValue + 652046,
    fullRecordGapCenterValue + 652166,
    fullRecordGapCenterValue + 652190,
    fullRecordGapCenterValue + 652226,
    fullRecordGapCenterValue + 652332,
    fullRecordGapCenterValue + 652436,
    fullRecordGapCenterValue + 652452,
    fullRecordGapCenterValue + 652502,
    fullRecordGapCenterValue + 652566,
    fullRecordGapCenterValue + 652836,
    fullRecordGapCenterValue + 652892,
    fullRecordGapCenterValue + 652926,
    fullRecordGapCenterValue + 652958,
    fullRecordGapCenterValue + 653006,
    fullRecordGapCenterValue + 653096,
    fullRecordGapCenterValue + 653222,
    fullRecordGapCenterValue + 653270,
    fullRecordGapCenterValue + 653282,
    fullRecordGapCenterValue + 653298,
    fullRecordGapCenterValue + 653336,
    fullRecordGapCenterValue + 653388,
    fullRecordGapCenterValue + 653402,
    fullRecordGapCenterValue + 653468,
    fullRecordGapCenterValue + 653502,
    fullRecordGapCenterValue + 653558,
    fullRecordGapCenterValue + 653628,
    fullRecordGapCenterValue + 653658,
    fullRecordGapCenterValue + 653738,
    fullRecordGapCenterValue + 653762,
    fullRecordGapCenterValue + 653816,
    fullRecordGapCenterValue + 653826,
    fullRecordGapCenterValue + 653846,
    fullRecordGapCenterValue + 653882,
    fullRecordGapCenterValue + 654006,
    fullRecordGapCenterValue + 654068,
    fullRecordGapCenterValue + 654230,
    fullRecordGapCenterValue + 654252,
    fullRecordGapCenterValue + 654266,
    fullRecordGapCenterValue + 654392,
    fullRecordGapCenterValue + 654438,
    fullRecordGapCenterValue + 654458,
    fullRecordGapCenterValue + 654582,
    fullRecordGapCenterValue + 654638,
    fullRecordGapCenterValue + 654686,
    fullRecordGapCenterValue + 654692,
    fullRecordGapCenterValue + 654708,
    fullRecordGapCenterValue + 654788,
    fullRecordGapCenterValue + 654866,
    fullRecordGapCenterValue + 654932,
    fullRecordGapCenterValue + 655022,
    fullRecordGapCenterValue + 655026,
    fullRecordGapCenterValue + 655058,
    fullRecordGapCenterValue + 655106,
    fullRecordGapCenterValue + 655208,
    fullRecordGapCenterValue + 655298,
    fullRecordGapCenterValue + 655370,
    fullRecordGapCenterValue + 655412]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00170_fermat : ∀ n ∈ fullRecordGapRow00170_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10817_not_prime : ¬(recordGapCenter + 651786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651786]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10818_not_prime : ¬(recordGapCenter + 651788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651788]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10819_not_prime : ¬(recordGapCenter + 651842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651842]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10820_not_prime : ¬(recordGapCenter + 651876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651876]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10821_not_prime : ¬(recordGapCenter + 651956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651956]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10822_not_prime : ¬(recordGapCenter + 651998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 651998]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10823_not_prime : ¬(recordGapCenter + 652022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 652022]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10824_not_prime : ¬(recordGapCenter + 652046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 652046]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10825_not_prime : ¬(recordGapCenter + 652166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 652166]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10826_not_prime : ¬(recordGapCenter + 652190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 652190]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10827_not_prime : ¬(recordGapCenter + 652226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 652226]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10828_not_prime : ¬(recordGapCenter + 652332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 652332]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10829_not_prime : ¬(recordGapCenter + 652436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 652436]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10830_not_prime : ¬(recordGapCenter + 652452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 652452]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10831_not_prime : ¬(recordGapCenter + 652502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 652502]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10832_not_prime : ¬(recordGapCenter + 652566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 652566]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10833_not_prime : ¬(recordGapCenter + 652836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 652836]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10834_not_prime : ¬(recordGapCenter + 652892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 652892]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10835_not_prime : ¬(recordGapCenter + 652926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 652926]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10836_not_prime : ¬(recordGapCenter + 652958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 652958]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10837_not_prime : ¬(recordGapCenter + 653006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653006]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10838_not_prime : ¬(recordGapCenter + 653096).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653096]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10839_not_prime : ¬(recordGapCenter + 653222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653222]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10840_not_prime : ¬(recordGapCenter + 653270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653270]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10841_not_prime : ¬(recordGapCenter + 653282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653282]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10842_not_prime : ¬(recordGapCenter + 653298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653298]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10843_not_prime : ¬(recordGapCenter + 653336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653336]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10844_not_prime : ¬(recordGapCenter + 653388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653388]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10845_not_prime : ¬(recordGapCenter + 653402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653402]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10846_not_prime : ¬(recordGapCenter + 653468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653468]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10847_not_prime : ¬(recordGapCenter + 653502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653502]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10848_not_prime : ¬(recordGapCenter + 653558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653558]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10849_not_prime : ¬(recordGapCenter + 653628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653628]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10850_not_prime : ¬(recordGapCenter + 653658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653658]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10851_not_prime : ¬(recordGapCenter + 653738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653738]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10852_not_prime : ¬(recordGapCenter + 653762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653762]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10853_not_prime : ¬(recordGapCenter + 653816).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653816]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10854_not_prime : ¬(recordGapCenter + 653826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653826]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10855_not_prime : ¬(recordGapCenter + 653846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653846]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10856_not_prime : ¬(recordGapCenter + 653882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 653882]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10857_not_prime : ¬(recordGapCenter + 654006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654006]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10858_not_prime : ¬(recordGapCenter + 654068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654068]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10859_not_prime : ¬(recordGapCenter + 654230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654230]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10860_not_prime : ¬(recordGapCenter + 654252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654252]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10861_not_prime : ¬(recordGapCenter + 654266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654266]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10862_not_prime : ¬(recordGapCenter + 654392).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654392]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10863_not_prime : ¬(recordGapCenter + 654438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654438]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10864_not_prime : ¬(recordGapCenter + 654458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654458]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10865_not_prime : ¬(recordGapCenter + 654582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654582]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10866_not_prime : ¬(recordGapCenter + 654638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654638]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10867_not_prime : ¬(recordGapCenter + 654686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654686]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10868_not_prime : ¬(recordGapCenter + 654692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654692]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10869_not_prime : ¬(recordGapCenter + 654708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654708]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10870_not_prime : ¬(recordGapCenter + 654788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654788]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10871_not_prime : ¬(recordGapCenter + 654866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654866]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10872_not_prime : ¬(recordGapCenter + 654932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 654932]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10873_not_prime : ¬(recordGapCenter + 655022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655022]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10874_not_prime : ¬(recordGapCenter + 655026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655026]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10875_not_prime : ¬(recordGapCenter + 655058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655058]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10876_not_prime : ¬(recordGapCenter + 655106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655106]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10877_not_prime : ¬(recordGapCenter + 655208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655208]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10878_not_prime : ¬(recordGapCenter + 655298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655298]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10879_not_prime : ¬(recordGapCenter + 655370).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655370]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

theorem fullRecordGapTerm10880_not_prime : ¬(recordGapCenter + 655412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 655412]
  · apply fullRecordGapRow00170_fermat
    simp [fullRecordGapRow00170_values]

end PrimeFactorUnimodality
