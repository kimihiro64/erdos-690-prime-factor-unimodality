import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue03841 : Nat := fullRecordGapCenterValue + 968

theorem fullRecordGapTerm03841_eq_value :
    recordGapCenter + 968 = fullRecordGapValue03841 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03841_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03841 (fullRecordGapValue03841 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03841_not_prime : ¬(recordGapCenter + 968).Prime := by
  rw [fullRecordGapTerm03841_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03841, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03841_fast_pow_mod_ne_one

def fullRecordGapValue03842 : Nat := fullRecordGapCenterValue + 990

theorem fullRecordGapTerm03842_eq_value :
    recordGapCenter + 990 = fullRecordGapValue03842 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03842_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03842 (fullRecordGapValue03842 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03842_not_prime : ¬(recordGapCenter + 990).Prime := by
  rw [fullRecordGapTerm03842_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03842, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03842_fast_pow_mod_ne_one

def fullRecordGapValue03843 : Nat := fullRecordGapCenterValue + 1050

theorem fullRecordGapTerm03843_eq_value :
    recordGapCenter + 1050 = fullRecordGapValue03843 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03843_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03843 (fullRecordGapValue03843 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03843_not_prime : ¬(recordGapCenter + 1050).Prime := by
  rw [fullRecordGapTerm03843_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03843, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03843_fast_pow_mod_ne_one

def fullRecordGapValue03844 : Nat := fullRecordGapCenterValue + 1200

theorem fullRecordGapTerm03844_eq_value :
    recordGapCenter + 1200 = fullRecordGapValue03844 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03844_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03844 (fullRecordGapValue03844 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03844_not_prime : ¬(recordGapCenter + 1200).Prime := by
  rw [fullRecordGapTerm03844_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03844, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03844_fast_pow_mod_ne_one

def fullRecordGapValue03845 : Nat := fullRecordGapCenterValue + 1260

theorem fullRecordGapTerm03845_eq_value :
    recordGapCenter + 1260 = fullRecordGapValue03845 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03845_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03845 (fullRecordGapValue03845 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03845_not_prime : ¬(recordGapCenter + 1260).Prime := by
  rw [fullRecordGapTerm03845_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03845, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03845_fast_pow_mod_ne_one

def fullRecordGapValue03846 : Nat := fullRecordGapCenterValue + 1320

theorem fullRecordGapTerm03846_eq_value :
    recordGapCenter + 1320 = fullRecordGapValue03846 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03846_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03846 (fullRecordGapValue03846 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03846_not_prime : ¬(recordGapCenter + 1320).Prime := by
  rw [fullRecordGapTerm03846_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03846, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03846_fast_pow_mod_ne_one

def fullRecordGapValue03847 : Nat := fullRecordGapCenterValue + 1386

theorem fullRecordGapTerm03847_eq_value :
    recordGapCenter + 1386 = fullRecordGapValue03847 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03847_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03847 (fullRecordGapValue03847 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03847_not_prime : ¬(recordGapCenter + 1386).Prime := by
  rw [fullRecordGapTerm03847_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03847, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03847_fast_pow_mod_ne_one

def fullRecordGapValue03848 : Nat := fullRecordGapCenterValue + 1452

theorem fullRecordGapTerm03848_eq_value :
    recordGapCenter + 1452 = fullRecordGapValue03848 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03848_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03848 (fullRecordGapValue03848 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03848_not_prime : ¬(recordGapCenter + 1452).Prime := by
  rw [fullRecordGapTerm03848_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03848, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03848_fast_pow_mod_ne_one

def fullRecordGapValue03849 : Nat := fullRecordGapCenterValue + 1500

theorem fullRecordGapTerm03849_eq_value :
    recordGapCenter + 1500 = fullRecordGapValue03849 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03849_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03849 (fullRecordGapValue03849 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03849_not_prime : ¬(recordGapCenter + 1500).Prime := by
  rw [fullRecordGapTerm03849_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03849, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03849_fast_pow_mod_ne_one

def fullRecordGapValue03850 : Nat := fullRecordGapCenterValue + 1620

theorem fullRecordGapTerm03850_eq_value :
    recordGapCenter + 1620 = fullRecordGapValue03850 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03850_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03850 (fullRecordGapValue03850 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03850_not_prime : ¬(recordGapCenter + 1620).Prime := by
  rw [fullRecordGapTerm03850_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03850, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03850_fast_pow_mod_ne_one

def fullRecordGapValue03851 : Nat := fullRecordGapCenterValue + 1650

theorem fullRecordGapTerm03851_eq_value :
    recordGapCenter + 1650 = fullRecordGapValue03851 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03851_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03851 (fullRecordGapValue03851 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03851_not_prime : ¬(recordGapCenter + 1650).Prime := by
  rw [fullRecordGapTerm03851_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03851, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03851_fast_pow_mod_ne_one

def fullRecordGapValue03852 : Nat := fullRecordGapCenterValue + 1680

theorem fullRecordGapTerm03852_eq_value :
    recordGapCenter + 1680 = fullRecordGapValue03852 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03852_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03852 (fullRecordGapValue03852 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03852_not_prime : ¬(recordGapCenter + 1680).Prime := by
  rw [fullRecordGapTerm03852_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03852, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03852_fast_pow_mod_ne_one

def fullRecordGapValue03853 : Nat := fullRecordGapCenterValue + 1782

theorem fullRecordGapTerm03853_eq_value :
    recordGapCenter + 1782 = fullRecordGapValue03853 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03853_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03853 (fullRecordGapValue03853 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03853_not_prime : ¬(recordGapCenter + 1782).Prime := by
  rw [fullRecordGapTerm03853_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03853, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03853_fast_pow_mod_ne_one

def fullRecordGapValue03854 : Nat := fullRecordGapCenterValue + 1848

theorem fullRecordGapTerm03854_eq_value :
    recordGapCenter + 1848 = fullRecordGapValue03854 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03854_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03854 (fullRecordGapValue03854 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03854_not_prime : ¬(recordGapCenter + 1848).Prime := by
  rw [fullRecordGapTerm03854_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03854, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03854_fast_pow_mod_ne_one

def fullRecordGapValue03855 : Nat := fullRecordGapCenterValue + 2016

theorem fullRecordGapTerm03855_eq_value :
    recordGapCenter + 2016 = fullRecordGapValue03855 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03855_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03855 (fullRecordGapValue03855 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03855_not_prime : ¬(recordGapCenter + 2016).Prime := by
  rw [fullRecordGapTerm03855_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03855, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03855_fast_pow_mod_ne_one

def fullRecordGapValue03856 : Nat := fullRecordGapCenterValue + 2048

theorem fullRecordGapTerm03856_eq_value :
    recordGapCenter + 2048 = fullRecordGapValue03856 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03856_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03856 (fullRecordGapValue03856 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03856_not_prime : ¬(recordGapCenter + 2048).Prime := by
  rw [fullRecordGapTerm03856_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03856, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03856_fast_pow_mod_ne_one

def fullRecordGapValue03857 : Nat := fullRecordGapCenterValue + 2058

theorem fullRecordGapTerm03857_eq_value :
    recordGapCenter + 2058 = fullRecordGapValue03857 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03857_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03857 (fullRecordGapValue03857 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03857_not_prime : ¬(recordGapCenter + 2058).Prime := by
  rw [fullRecordGapTerm03857_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03857, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03857_fast_pow_mod_ne_one

def fullRecordGapValue03858 : Nat := fullRecordGapCenterValue + 2100

theorem fullRecordGapTerm03858_eq_value :
    recordGapCenter + 2100 = fullRecordGapValue03858 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03858_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03858 (fullRecordGapValue03858 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03858_not_prime : ¬(recordGapCenter + 2100).Prime := by
  rw [fullRecordGapTerm03858_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03858, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03858_fast_pow_mod_ne_one

def fullRecordGapValue03859 : Nat := fullRecordGapCenterValue + 2112

theorem fullRecordGapTerm03859_eq_value :
    recordGapCenter + 2112 = fullRecordGapValue03859 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03859_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03859 (fullRecordGapValue03859 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03859_not_prime : ¬(recordGapCenter + 2112).Prime := by
  rw [fullRecordGapTerm03859_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03859, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03859_fast_pow_mod_ne_one

def fullRecordGapValue03860 : Nat := fullRecordGapCenterValue + 2156

theorem fullRecordGapTerm03860_eq_value :
    recordGapCenter + 2156 = fullRecordGapValue03860 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03860_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03860 (fullRecordGapValue03860 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03860_not_prime : ¬(recordGapCenter + 2156).Prime := by
  rw [fullRecordGapTerm03860_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03860, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03860_fast_pow_mod_ne_one

def fullRecordGapValue03861 : Nat := fullRecordGapCenterValue + 2160

theorem fullRecordGapTerm03861_eq_value :
    recordGapCenter + 2160 = fullRecordGapValue03861 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03861_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03861 (fullRecordGapValue03861 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03861_not_prime : ¬(recordGapCenter + 2160).Prime := by
  rw [fullRecordGapTerm03861_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03861, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03861_fast_pow_mod_ne_one

def fullRecordGapValue03862 : Nat := fullRecordGapCenterValue + 2178

theorem fullRecordGapTerm03862_eq_value :
    recordGapCenter + 2178 = fullRecordGapValue03862 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03862_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03862 (fullRecordGapValue03862 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03862_not_prime : ¬(recordGapCenter + 2178).Prime := by
  rw [fullRecordGapTerm03862_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03862, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03862_fast_pow_mod_ne_one

def fullRecordGapValue03863 : Nat := fullRecordGapCenterValue + 2352

theorem fullRecordGapTerm03863_eq_value :
    recordGapCenter + 2352 = fullRecordGapValue03863 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03863_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03863 (fullRecordGapValue03863 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03863_not_prime : ¬(recordGapCenter + 2352).Prime := by
  rw [fullRecordGapTerm03863_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03863, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03863_fast_pow_mod_ne_one

def fullRecordGapValue03864 : Nat := fullRecordGapCenterValue + 2376

theorem fullRecordGapTerm03864_eq_value :
    recordGapCenter + 2376 = fullRecordGapValue03864 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03864_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03864 (fullRecordGapValue03864 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03864_not_prime : ¬(recordGapCenter + 2376).Prime := by
  rw [fullRecordGapTerm03864_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03864, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03864_fast_pow_mod_ne_one

def fullRecordGapValue03865 : Nat := fullRecordGapCenterValue + 2430

theorem fullRecordGapTerm03865_eq_value :
    recordGapCenter + 2430 = fullRecordGapValue03865 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03865_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03865 (fullRecordGapValue03865 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03865_not_prime : ¬(recordGapCenter + 2430).Prime := by
  rw [fullRecordGapTerm03865_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03865, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03865_fast_pow_mod_ne_one

def fullRecordGapValue03866 : Nat := fullRecordGapCenterValue + 2450

theorem fullRecordGapTerm03866_eq_value :
    recordGapCenter + 2450 = fullRecordGapValue03866 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03866_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03866 (fullRecordGapValue03866 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03866_not_prime : ¬(recordGapCenter + 2450).Prime := by
  rw [fullRecordGapTerm03866_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03866, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03866_fast_pow_mod_ne_one

def fullRecordGapValue03867 : Nat := fullRecordGapCenterValue + 2640

theorem fullRecordGapTerm03867_eq_value :
    recordGapCenter + 2640 = fullRecordGapValue03867 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03867_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03867 (fullRecordGapValue03867 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03867_not_prime : ¬(recordGapCenter + 2640).Prime := by
  rw [fullRecordGapTerm03867_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03867, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03867_fast_pow_mod_ne_one

def fullRecordGapValue03868 : Nat := fullRecordGapCenterValue + 2646

theorem fullRecordGapTerm03868_eq_value :
    recordGapCenter + 2646 = fullRecordGapValue03868 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03868_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03868 (fullRecordGapValue03868 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03868_not_prime : ¬(recordGapCenter + 2646).Prime := by
  rw [fullRecordGapTerm03868_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03868, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03868_fast_pow_mod_ne_one

def fullRecordGapValue03869 : Nat := fullRecordGapCenterValue + 2772

theorem fullRecordGapTerm03869_eq_value :
    recordGapCenter + 2772 = fullRecordGapValue03869 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03869_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03869 (fullRecordGapValue03869 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03869_not_prime : ¬(recordGapCenter + 2772).Prime := by
  rw [fullRecordGapTerm03869_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03869, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03869_fast_pow_mod_ne_one

def fullRecordGapValue03870 : Nat := fullRecordGapCenterValue + 2816

theorem fullRecordGapTerm03870_eq_value :
    recordGapCenter + 2816 = fullRecordGapValue03870 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03870_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03870 (fullRecordGapValue03870 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03870_not_prime : ¬(recordGapCenter + 2816).Prime := by
  rw [fullRecordGapTerm03870_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03870, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03870_fast_pow_mod_ne_one

def fullRecordGapValue03871 : Nat := fullRecordGapCenterValue + 2916

theorem fullRecordGapTerm03871_eq_value :
    recordGapCenter + 2916 = fullRecordGapValue03871 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03871_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03871 (fullRecordGapValue03871 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03871_not_prime : ¬(recordGapCenter + 2916).Prime := by
  rw [fullRecordGapTerm03871_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03871, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03871_fast_pow_mod_ne_one

def fullRecordGapValue03872 : Nat := fullRecordGapCenterValue + 2940

theorem fullRecordGapTerm03872_eq_value :
    recordGapCenter + 2940 = fullRecordGapValue03872 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03872_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03872 (fullRecordGapValue03872 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03872_not_prime : ¬(recordGapCenter + 2940).Prime := by
  rw [fullRecordGapTerm03872_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03872, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03872_fast_pow_mod_ne_one

def fullRecordGapValue03873 : Nat := fullRecordGapCenterValue + 2970

theorem fullRecordGapTerm03873_eq_value :
    recordGapCenter + 2970 = fullRecordGapValue03873 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03873_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03873 (fullRecordGapValue03873 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03873_not_prime : ¬(recordGapCenter + 2970).Prime := by
  rw [fullRecordGapTerm03873_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03873, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03873_fast_pow_mod_ne_one

def fullRecordGapValue03874 : Nat := fullRecordGapCenterValue + 3168

theorem fullRecordGapTerm03874_eq_value :
    recordGapCenter + 3168 = fullRecordGapValue03874 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03874_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03874 (fullRecordGapValue03874 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03874_not_prime : ¬(recordGapCenter + 3168).Prime := by
  rw [fullRecordGapTerm03874_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03874, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03874_fast_pow_mod_ne_one

def fullRecordGapValue03875 : Nat := fullRecordGapCenterValue + 3200

theorem fullRecordGapTerm03875_eq_value :
    recordGapCenter + 3200 = fullRecordGapValue03875 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03875_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03875 (fullRecordGapValue03875 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03875_not_prime : ¬(recordGapCenter + 3200).Prime := by
  rw [fullRecordGapTerm03875_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03875, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03875_fast_pow_mod_ne_one

def fullRecordGapValue03876 : Nat := fullRecordGapCenterValue + 3360

theorem fullRecordGapTerm03876_eq_value :
    recordGapCenter + 3360 = fullRecordGapValue03876 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03876_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03876 (fullRecordGapValue03876 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03876_not_prime : ¬(recordGapCenter + 3360).Prime := by
  rw [fullRecordGapTerm03876_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03876, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03876_fast_pow_mod_ne_one

def fullRecordGapValue03877 : Nat := fullRecordGapCenterValue + 3402

theorem fullRecordGapTerm03877_eq_value :
    recordGapCenter + 3402 = fullRecordGapValue03877 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03877_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03877 (fullRecordGapValue03877 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03877_not_prime : ¬(recordGapCenter + 3402).Prime := by
  rw [fullRecordGapTerm03877_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03877, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03877_fast_pow_mod_ne_one

def fullRecordGapValue03878 : Nat := fullRecordGapCenterValue + 3456

theorem fullRecordGapTerm03878_eq_value :
    recordGapCenter + 3456 = fullRecordGapValue03878 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03878_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03878 (fullRecordGapValue03878 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03878_not_prime : ¬(recordGapCenter + 3456).Prime := by
  rw [fullRecordGapTerm03878_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03878, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03878_fast_pow_mod_ne_one

def fullRecordGapValue03879 : Nat := fullRecordGapCenterValue + 3500

theorem fullRecordGapTerm03879_eq_value :
    recordGapCenter + 3500 = fullRecordGapValue03879 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03879_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03879 (fullRecordGapValue03879 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03879_not_prime : ¬(recordGapCenter + 3500).Prime := by
  rw [fullRecordGapTerm03879_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03879, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03879_fast_pow_mod_ne_one

def fullRecordGapValue03880 : Nat := fullRecordGapCenterValue + 3630

theorem fullRecordGapTerm03880_eq_value :
    recordGapCenter + 3630 = fullRecordGapValue03880 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03880_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03880 (fullRecordGapValue03880 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03880_not_prime : ¬(recordGapCenter + 3630).Prime := by
  rw [fullRecordGapTerm03880_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03880, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03880_fast_pow_mod_ne_one

def fullRecordGapValue03881 : Nat := fullRecordGapCenterValue + 3696

theorem fullRecordGapTerm03881_eq_value :
    recordGapCenter + 3696 = fullRecordGapValue03881 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03881_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03881 (fullRecordGapValue03881 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03881_not_prime : ¬(recordGapCenter + 3696).Prime := by
  rw [fullRecordGapTerm03881_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03881, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03881_fast_pow_mod_ne_one

def fullRecordGapValue03882 : Nat := fullRecordGapCenterValue + 3750

theorem fullRecordGapTerm03882_eq_value :
    recordGapCenter + 3750 = fullRecordGapValue03882 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03882_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03882 (fullRecordGapValue03882 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03882_not_prime : ¬(recordGapCenter + 3750).Prime := by
  rw [fullRecordGapTerm03882_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03882, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03882_fast_pow_mod_ne_one

def fullRecordGapValue03883 : Nat := fullRecordGapCenterValue + 3872

theorem fullRecordGapTerm03883_eq_value :
    recordGapCenter + 3872 = fullRecordGapValue03883 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03883_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03883 (fullRecordGapValue03883 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03883_not_prime : ¬(recordGapCenter + 3872).Prime := by
  rw [fullRecordGapTerm03883_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03883, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03883_fast_pow_mod_ne_one

def fullRecordGapValue03884 : Nat := fullRecordGapCenterValue + 3920

theorem fullRecordGapTerm03884_eq_value :
    recordGapCenter + 3920 = fullRecordGapValue03884 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03884_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03884 (fullRecordGapValue03884 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03884_not_prime : ¬(recordGapCenter + 3920).Prime := by
  rw [fullRecordGapTerm03884_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03884, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03884_fast_pow_mod_ne_one

def fullRecordGapValue03885 : Nat := fullRecordGapCenterValue + 3960

theorem fullRecordGapTerm03885_eq_value :
    recordGapCenter + 3960 = fullRecordGapValue03885 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03885_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03885 (fullRecordGapValue03885 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03885_not_prime : ¬(recordGapCenter + 3960).Prime := by
  rw [fullRecordGapTerm03885_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03885, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03885_fast_pow_mod_ne_one

def fullRecordGapValue03886 : Nat := fullRecordGapCenterValue + 4158

theorem fullRecordGapTerm03886_eq_value :
    recordGapCenter + 4158 = fullRecordGapValue03886 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03886_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03886 (fullRecordGapValue03886 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03886_not_prime : ¬(recordGapCenter + 4158).Prime := by
  rw [fullRecordGapTerm03886_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03886, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03886_fast_pow_mod_ne_one

def fullRecordGapValue03887 : Nat := fullRecordGapCenterValue + 4320

theorem fullRecordGapTerm03887_eq_value :
    recordGapCenter + 4320 = fullRecordGapValue03887 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03887_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03887 (fullRecordGapValue03887 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03887_not_prime : ¬(recordGapCenter + 4320).Prime := by
  rw [fullRecordGapTerm03887_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03887, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03887_fast_pow_mod_ne_one

def fullRecordGapValue03888 : Nat := fullRecordGapCenterValue + 4536

theorem fullRecordGapTerm03888_eq_value :
    recordGapCenter + 4536 = fullRecordGapValue03888 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03888_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03888 (fullRecordGapValue03888 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03888_not_prime : ¬(recordGapCenter + 4536).Prime := by
  rw [fullRecordGapTerm03888_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03888, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03888_fast_pow_mod_ne_one

def fullRecordGapValue03889 : Nat := fullRecordGapCenterValue + 4608

theorem fullRecordGapTerm03889_eq_value :
    recordGapCenter + 4608 = fullRecordGapValue03889 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03889_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03889 (fullRecordGapValue03889 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03889_not_prime : ¬(recordGapCenter + 4608).Prime := by
  rw [fullRecordGapTerm03889_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03889, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03889_fast_pow_mod_ne_one

def fullRecordGapValue03890 : Nat := fullRecordGapCenterValue + 4860

theorem fullRecordGapTerm03890_eq_value :
    recordGapCenter + 4860 = fullRecordGapValue03890 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03890_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03890 (fullRecordGapValue03890 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03890_not_prime : ¬(recordGapCenter + 4860).Prime := by
  rw [fullRecordGapTerm03890_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03890, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03890_fast_pow_mod_ne_one

def fullRecordGapValue03891 : Nat := fullRecordGapCenterValue + 4928

theorem fullRecordGapTerm03891_eq_value :
    recordGapCenter + 4928 = fullRecordGapValue03891 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03891_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03891 (fullRecordGapValue03891 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03891_not_prime : ¬(recordGapCenter + 4928).Prime := by
  rw [fullRecordGapTerm03891_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03891, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03891_fast_pow_mod_ne_one

def fullRecordGapValue03892 : Nat := fullRecordGapCenterValue + 4950

theorem fullRecordGapTerm03892_eq_value :
    recordGapCenter + 4950 = fullRecordGapValue03892 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03892_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03892 (fullRecordGapValue03892 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03892_not_prime : ¬(recordGapCenter + 4950).Prime := by
  rw [fullRecordGapTerm03892_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03892, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03892_fast_pow_mod_ne_one

def fullRecordGapValue03893 : Nat := fullRecordGapCenterValue + 5000

theorem fullRecordGapTerm03893_eq_value :
    recordGapCenter + 5000 = fullRecordGapValue03893 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03893_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03893 (fullRecordGapValue03893 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03893_not_prime : ¬(recordGapCenter + 5000).Prime := by
  rw [fullRecordGapTerm03893_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03893, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03893_fast_pow_mod_ne_one

def fullRecordGapValue03894 : Nat := fullRecordGapCenterValue + 5120

theorem fullRecordGapTerm03894_eq_value :
    recordGapCenter + 5120 = fullRecordGapValue03894 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03894_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03894 (fullRecordGapValue03894 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03894_not_prime : ¬(recordGapCenter + 5120).Prime := by
  rw [fullRecordGapTerm03894_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03894, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03894_fast_pow_mod_ne_one

def fullRecordGapValue03895 : Nat := fullRecordGapCenterValue + 5280

theorem fullRecordGapTerm03895_eq_value :
    recordGapCenter + 5280 = fullRecordGapValue03895 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03895_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03895 (fullRecordGapValue03895 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03895_not_prime : ¬(recordGapCenter + 5280).Prime := by
  rw [fullRecordGapTerm03895_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03895, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03895_fast_pow_mod_ne_one

def fullRecordGapValue03896 : Nat := fullRecordGapCenterValue + 5292

theorem fullRecordGapTerm03896_eq_value :
    recordGapCenter + 5292 = fullRecordGapValue03896 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03896_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03896 (fullRecordGapValue03896 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03896_not_prime : ¬(recordGapCenter + 5292).Prime := by
  rw [fullRecordGapTerm03896_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03896, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03896_fast_pow_mod_ne_one

def fullRecordGapValue03897 : Nat := fullRecordGapCenterValue + 5346

theorem fullRecordGapTerm03897_eq_value :
    recordGapCenter + 5346 = fullRecordGapValue03897 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03897_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03897 (fullRecordGapValue03897 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03897_not_prime : ¬(recordGapCenter + 5346).Prime := by
  rw [fullRecordGapTerm03897_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03897, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03897_fast_pow_mod_ne_one

def fullRecordGapValue03898 : Nat := fullRecordGapCenterValue + 5390

theorem fullRecordGapTerm03898_eq_value :
    recordGapCenter + 5390 = fullRecordGapValue03898 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03898_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03898 (fullRecordGapValue03898 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03898_not_prime : ¬(recordGapCenter + 5390).Prime := by
  rw [fullRecordGapTerm03898_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03898, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03898_fast_pow_mod_ne_one

def fullRecordGapValue03899 : Nat := fullRecordGapCenterValue + 5670

theorem fullRecordGapTerm03899_eq_value :
    recordGapCenter + 5670 = fullRecordGapValue03899 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03899_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03899 (fullRecordGapValue03899 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03899_not_prime : ¬(recordGapCenter + 5670).Prime := by
  rw [fullRecordGapTerm03899_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03899, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03899_fast_pow_mod_ne_one

def fullRecordGapValue03900 : Nat := fullRecordGapCenterValue + 5808

theorem fullRecordGapTerm03900_eq_value :
    recordGapCenter + 5808 = fullRecordGapValue03900 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03900_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03900 (fullRecordGapValue03900 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03900_not_prime : ¬(recordGapCenter + 5808).Prime := by
  rw [fullRecordGapTerm03900_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03900, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03900_fast_pow_mod_ne_one

def fullRecordGapValue03901 : Nat := fullRecordGapCenterValue + 5832

theorem fullRecordGapTerm03901_eq_value :
    recordGapCenter + 5832 = fullRecordGapValue03901 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03901_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03901 (fullRecordGapValue03901 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03901_not_prime : ¬(recordGapCenter + 5832).Prime := by
  rw [fullRecordGapTerm03901_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03901, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03901_fast_pow_mod_ne_one

def fullRecordGapValue03902 : Nat := fullRecordGapCenterValue + 5880

theorem fullRecordGapTerm03902_eq_value :
    recordGapCenter + 5880 = fullRecordGapValue03902 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03902_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03902 (fullRecordGapValue03902 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03902_not_prime : ¬(recordGapCenter + 5880).Prime := by
  rw [fullRecordGapTerm03902_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03902, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03902_fast_pow_mod_ne_one

def fullRecordGapValue03903 : Nat := fullRecordGapCenterValue + 6300

theorem fullRecordGapTerm03903_eq_value :
    recordGapCenter + 6300 = fullRecordGapValue03903 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03903_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03903 (fullRecordGapValue03903 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03903_not_prime : ¬(recordGapCenter + 6300).Prime := by
  rw [fullRecordGapTerm03903_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03903, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03903_fast_pow_mod_ne_one

def fullRecordGapValue03904 : Nat := fullRecordGapCenterValue + 6336

theorem fullRecordGapTerm03904_eq_value :
    recordGapCenter + 6336 = fullRecordGapValue03904 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03904_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03904 (fullRecordGapValue03904 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03904_not_prime : ¬(recordGapCenter + 6336).Prime := by
  rw [fullRecordGapTerm03904_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03904, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03904_fast_pow_mod_ne_one

def fullRecordGapValue03905 : Nat := fullRecordGapCenterValue + 6480

theorem fullRecordGapTerm03905_eq_value :
    recordGapCenter + 6480 = fullRecordGapValue03905 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03905_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03905 (fullRecordGapValue03905 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03905_not_prime : ¬(recordGapCenter + 6480).Prime := by
  rw [fullRecordGapTerm03905_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03905, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03905_fast_pow_mod_ne_one

def fullRecordGapValue03906 : Nat := fullRecordGapCenterValue + 6720

theorem fullRecordGapTerm03906_eq_value :
    recordGapCenter + 6720 = fullRecordGapValue03906 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03906_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03906 (fullRecordGapValue03906 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03906_not_prime : ¬(recordGapCenter + 6720).Prime := by
  rw [fullRecordGapTerm03906_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03906, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03906_fast_pow_mod_ne_one

def fullRecordGapValue03907 : Nat := fullRecordGapCenterValue + 7056

theorem fullRecordGapTerm03907_eq_value :
    recordGapCenter + 7056 = fullRecordGapValue03907 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03907_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03907 (fullRecordGapValue03907 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03907_not_prime : ¬(recordGapCenter + 7056).Prime := by
  rw [fullRecordGapTerm03907_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03907, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03907_fast_pow_mod_ne_one

def fullRecordGapValue03908 : Nat := fullRecordGapCenterValue + 7128

theorem fullRecordGapTerm03908_eq_value :
    recordGapCenter + 7128 = fullRecordGapValue03908 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03908_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03908 (fullRecordGapValue03908 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03908_not_prime : ¬(recordGapCenter + 7128).Prime := by
  rw [fullRecordGapTerm03908_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03908, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03908_fast_pow_mod_ne_one

def fullRecordGapValue03909 : Nat := fullRecordGapCenterValue + 7290

theorem fullRecordGapTerm03909_eq_value :
    recordGapCenter + 7290 = fullRecordGapValue03909 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03909_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03909 (fullRecordGapValue03909 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03909_not_prime : ¬(recordGapCenter + 7290).Prime := by
  rw [fullRecordGapTerm03909_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03909, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03909_fast_pow_mod_ne_one

def fullRecordGapValue03910 : Nat := fullRecordGapCenterValue + 7500

theorem fullRecordGapTerm03910_eq_value :
    recordGapCenter + 7500 = fullRecordGapValue03910 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03910_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03910 (fullRecordGapValue03910 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03910_not_prime : ¬(recordGapCenter + 7500).Prime := by
  rw [fullRecordGapTerm03910_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03910, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03910_fast_pow_mod_ne_one

def fullRecordGapValue03911 : Nat := fullRecordGapCenterValue + 7560

theorem fullRecordGapTerm03911_eq_value :
    recordGapCenter + 7560 = fullRecordGapValue03911 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03911_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03911 (fullRecordGapValue03911 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03911_not_prime : ¬(recordGapCenter + 7560).Prime := by
  rw [fullRecordGapTerm03911_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03911, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03911_fast_pow_mod_ne_one

def fullRecordGapValue03912 : Nat := fullRecordGapCenterValue + 7920

theorem fullRecordGapTerm03912_eq_value :
    recordGapCenter + 7920 = fullRecordGapValue03912 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03912_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03912 (fullRecordGapValue03912 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03912_not_prime : ¬(recordGapCenter + 7920).Prime := by
  rw [fullRecordGapTerm03912_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03912, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03912_fast_pow_mod_ne_one

def fullRecordGapValue03913 : Nat := fullRecordGapCenterValue + 8192

theorem fullRecordGapTerm03913_eq_value :
    recordGapCenter + 8192 = fullRecordGapValue03913 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03913_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03913 (fullRecordGapValue03913 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03913_not_prime : ¬(recordGapCenter + 8192).Prime := by
  rw [fullRecordGapTerm03913_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03913, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03913_fast_pow_mod_ne_one

def fullRecordGapValue03914 : Nat := fullRecordGapCenterValue + 8712

theorem fullRecordGapTerm03914_eq_value :
    recordGapCenter + 8712 = fullRecordGapValue03914 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03914_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03914 (fullRecordGapValue03914 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03914_not_prime : ¬(recordGapCenter + 8712).Prime := by
  rw [fullRecordGapTerm03914_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03914, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03914_fast_pow_mod_ne_one

def fullRecordGapValue03915 : Nat := fullRecordGapCenterValue + 8748

theorem fullRecordGapTerm03915_eq_value :
    recordGapCenter + 8748 = fullRecordGapValue03915 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03915_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03915 (fullRecordGapValue03915 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03915_not_prime : ¬(recordGapCenter + 8748).Prime := by
  rw [fullRecordGapTerm03915_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03915, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03915_fast_pow_mod_ne_one

def fullRecordGapValue03916 : Nat := fullRecordGapCenterValue + 8750

theorem fullRecordGapTerm03916_eq_value :
    recordGapCenter + 8750 = fullRecordGapValue03916 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03916_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03916 (fullRecordGapValue03916 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03916_not_prime : ¬(recordGapCenter + 8750).Prime := by
  rw [fullRecordGapTerm03916_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03916, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03916_fast_pow_mod_ne_one

def fullRecordGapValue03917 : Nat := fullRecordGapCenterValue + 9000

theorem fullRecordGapTerm03917_eq_value :
    recordGapCenter + 9000 = fullRecordGapValue03917 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03917_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03917 (fullRecordGapValue03917 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03917_not_prime : ¬(recordGapCenter + 9000).Prime := by
  rw [fullRecordGapTerm03917_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03917, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03917_fast_pow_mod_ne_one

def fullRecordGapValue03918 : Nat := fullRecordGapCenterValue + 9216

theorem fullRecordGapTerm03918_eq_value :
    recordGapCenter + 9216 = fullRecordGapValue03918 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03918_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03918 (fullRecordGapValue03918 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03918_not_prime : ¬(recordGapCenter + 9216).Prime := by
  rw [fullRecordGapTerm03918_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03918, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03918_fast_pow_mod_ne_one

def fullRecordGapValue03919 : Nat := fullRecordGapCenterValue + 9240

theorem fullRecordGapTerm03919_eq_value :
    recordGapCenter + 9240 = fullRecordGapValue03919 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03919_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03919 (fullRecordGapValue03919 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03919_not_prime : ¬(recordGapCenter + 9240).Prime := by
  rw [fullRecordGapTerm03919_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03919, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03919_fast_pow_mod_ne_one

def fullRecordGapValue03920 : Nat := fullRecordGapCenterValue + 9408

theorem fullRecordGapTerm03920_eq_value :
    recordGapCenter + 9408 = fullRecordGapValue03920 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03920_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03920 (fullRecordGapValue03920 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03920_not_prime : ¬(recordGapCenter + 9408).Prime := by
  rw [fullRecordGapTerm03920_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03920, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03920_fast_pow_mod_ne_one

def fullRecordGapValue03921 : Nat := fullRecordGapCenterValue + 9600

theorem fullRecordGapTerm03921_eq_value :
    recordGapCenter + 9600 = fullRecordGapValue03921 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03921_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03921 (fullRecordGapValue03921 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03921_not_prime : ¬(recordGapCenter + 9600).Prime := by
  rw [fullRecordGapTerm03921_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03921, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03921_fast_pow_mod_ne_one

def fullRecordGapValue03922 : Nat := fullRecordGapCenterValue + 9702

theorem fullRecordGapTerm03922_eq_value :
    recordGapCenter + 9702 = fullRecordGapValue03922 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03922_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03922 (fullRecordGapValue03922 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03922_not_prime : ¬(recordGapCenter + 9702).Prime := by
  rw [fullRecordGapTerm03922_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03922, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03922_fast_pow_mod_ne_one

def fullRecordGapValue03923 : Nat := fullRecordGapCenterValue + 9900

theorem fullRecordGapTerm03923_eq_value :
    recordGapCenter + 9900 = fullRecordGapValue03923 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03923_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03923 (fullRecordGapValue03923 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03923_not_prime : ¬(recordGapCenter + 9900).Prime := by
  rw [fullRecordGapTerm03923_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03923, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03923_fast_pow_mod_ne_one

def fullRecordGapValue03924 : Nat := fullRecordGapCenterValue + 10368

theorem fullRecordGapTerm03924_eq_value :
    recordGapCenter + 10368 = fullRecordGapValue03924 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03924_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03924 (fullRecordGapValue03924 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03924_not_prime : ¬(recordGapCenter + 10368).Prime := by
  rw [fullRecordGapTerm03924_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03924, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03924_fast_pow_mod_ne_one

def fullRecordGapValue03925 : Nat := fullRecordGapCenterValue + 10692

theorem fullRecordGapTerm03925_eq_value :
    recordGapCenter + 10692 = fullRecordGapValue03925 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03925_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03925 (fullRecordGapValue03925 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03925_not_prime : ¬(recordGapCenter + 10692).Prime := by
  rw [fullRecordGapTerm03925_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03925, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03925_fast_pow_mod_ne_one

def fullRecordGapValue03926 : Nat := fullRecordGapCenterValue + 10976

theorem fullRecordGapTerm03926_eq_value :
    recordGapCenter + 10976 = fullRecordGapValue03926 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03926_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03926 (fullRecordGapValue03926 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03926_not_prime : ¬(recordGapCenter + 10976).Prime := by
  rw [fullRecordGapTerm03926_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03926, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03926_fast_pow_mod_ne_one

def fullRecordGapValue03927 : Nat := fullRecordGapCenterValue + 12000

theorem fullRecordGapTerm03927_eq_value :
    recordGapCenter + 12000 = fullRecordGapValue03927 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03927_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03927 (fullRecordGapValue03927 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03927_not_prime : ¬(recordGapCenter + 12000).Prime := by
  rw [fullRecordGapTerm03927_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03927, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03927_fast_pow_mod_ne_one

def fullRecordGapValue03928 : Nat := fullRecordGapCenterValue + 12320

theorem fullRecordGapTerm03928_eq_value :
    recordGapCenter + 12320 = fullRecordGapValue03928 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03928_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03928 (fullRecordGapValue03928 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03928_not_prime : ¬(recordGapCenter + 12320).Prime := by
  rw [fullRecordGapTerm03928_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03928, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03928_fast_pow_mod_ne_one

def fullRecordGapValue03929 : Nat := fullRecordGapCenterValue + 12348

theorem fullRecordGapTerm03929_eq_value :
    recordGapCenter + 12348 = fullRecordGapValue03929 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03929_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03929 (fullRecordGapValue03929 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03929_not_prime : ¬(recordGapCenter + 12348).Prime := by
  rw [fullRecordGapTerm03929_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03929, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03929_fast_pow_mod_ne_one

def fullRecordGapValue03930 : Nat := fullRecordGapCenterValue + 12500

theorem fullRecordGapTerm03930_eq_value :
    recordGapCenter + 12500 = fullRecordGapValue03930 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03930_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03930 (fullRecordGapValue03930 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03930_not_prime : ¬(recordGapCenter + 12500).Prime := by
  rw [fullRecordGapTerm03930_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03930, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03930_fast_pow_mod_ne_one

def fullRecordGapValue03931 : Nat := fullRecordGapCenterValue + 12600

theorem fullRecordGapTerm03931_eq_value :
    recordGapCenter + 12600 = fullRecordGapValue03931 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03931_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03931 (fullRecordGapValue03931 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03931_not_prime : ¬(recordGapCenter + 12600).Prime := by
  rw [fullRecordGapTerm03931_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03931, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03931_fast_pow_mod_ne_one

def fullRecordGapValue03932 : Nat := fullRecordGapCenterValue + 13230

theorem fullRecordGapTerm03932_eq_value :
    recordGapCenter + 13230 = fullRecordGapValue03932 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03932_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03932 (fullRecordGapValue03932 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03932_not_prime : ¬(recordGapCenter + 13230).Prime := by
  rw [fullRecordGapTerm03932_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03932, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03932_fast_pow_mod_ne_one

def fullRecordGapValue03933 : Nat := fullRecordGapCenterValue + 13310

theorem fullRecordGapTerm03933_eq_value :
    recordGapCenter + 13310 = fullRecordGapValue03933 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03933_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03933 (fullRecordGapValue03933 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03933_not_prime : ¬(recordGapCenter + 13310).Prime := by
  rw [fullRecordGapTerm03933_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03933, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03933_fast_pow_mod_ne_one

def fullRecordGapValue03934 : Nat := fullRecordGapCenterValue + 13440

theorem fullRecordGapTerm03934_eq_value :
    recordGapCenter + 13440 = fullRecordGapValue03934 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03934_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03934 (fullRecordGapValue03934 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03934_not_prime : ¬(recordGapCenter + 13440).Prime := by
  rw [fullRecordGapTerm03934_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03934, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03934_fast_pow_mod_ne_one

def fullRecordGapValue03935 : Nat := fullRecordGapCenterValue + 13860

theorem fullRecordGapTerm03935_eq_value :
    recordGapCenter + 13860 = fullRecordGapValue03935 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03935_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03935 (fullRecordGapValue03935 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03935_not_prime : ¬(recordGapCenter + 13860).Prime := by
  rw [fullRecordGapTerm03935_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03935, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03935_fast_pow_mod_ne_one

def fullRecordGapValue03936 : Nat := fullRecordGapCenterValue + 14112

theorem fullRecordGapTerm03936_eq_value :
    recordGapCenter + 14112 = fullRecordGapValue03936 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03936_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03936 (fullRecordGapValue03936 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03936_not_prime : ¬(recordGapCenter + 14112).Prime := by
  rw [fullRecordGapTerm03936_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03936, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03936_fast_pow_mod_ne_one

def fullRecordGapValue03937 : Nat := fullRecordGapCenterValue + 14336

theorem fullRecordGapTerm03937_eq_value :
    recordGapCenter + 14336 = fullRecordGapValue03937 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03937_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03937 (fullRecordGapValue03937 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03937_not_prime : ¬(recordGapCenter + 14336).Prime := by
  rw [fullRecordGapTerm03937_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03937, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03937_fast_pow_mod_ne_one

def fullRecordGapValue03938 : Nat := fullRecordGapCenterValue + 14400

theorem fullRecordGapTerm03938_eq_value :
    recordGapCenter + 14400 = fullRecordGapValue03938 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03938_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03938 (fullRecordGapValue03938 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03938_not_prime : ¬(recordGapCenter + 14400).Prime := by
  rw [fullRecordGapTerm03938_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03938, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03938_fast_pow_mod_ne_one

def fullRecordGapValue03939 : Nat := fullRecordGapCenterValue + 14850

theorem fullRecordGapTerm03939_eq_value :
    recordGapCenter + 14850 = fullRecordGapValue03939 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03939_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03939 (fullRecordGapValue03939 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03939_not_prime : ¬(recordGapCenter + 14850).Prime := by
  rw [fullRecordGapTerm03939_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03939, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03939_fast_pow_mod_ne_one

def fullRecordGapValue03940 : Nat := fullRecordGapCenterValue + 15246

theorem fullRecordGapTerm03940_eq_value :
    recordGapCenter + 15246 = fullRecordGapValue03940 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03940_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03940 (fullRecordGapValue03940 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03940_not_prime : ¬(recordGapCenter + 15246).Prime := by
  rw [fullRecordGapTerm03940_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03940, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03940_fast_pow_mod_ne_one

def fullRecordGapValue03941 : Nat := fullRecordGapCenterValue + 15750

theorem fullRecordGapTerm03941_eq_value :
    recordGapCenter + 15750 = fullRecordGapValue03941 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03941_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03941 (fullRecordGapValue03941 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03941_not_prime : ¬(recordGapCenter + 15750).Prime := by
  rw [fullRecordGapTerm03941_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03941, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03941_fast_pow_mod_ne_one

def fullRecordGapValue03942 : Nat := fullRecordGapCenterValue + 16170

theorem fullRecordGapTerm03942_eq_value :
    recordGapCenter + 16170 = fullRecordGapValue03942 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03942_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03942 (fullRecordGapValue03942 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03942_not_prime : ¬(recordGapCenter + 16170).Prime := by
  rw [fullRecordGapTerm03942_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03942, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03942_fast_pow_mod_ne_one

def fullRecordGapValue03943 : Nat := fullRecordGapCenterValue + 16200

theorem fullRecordGapTerm03943_eq_value :
    recordGapCenter + 16200 = fullRecordGapValue03943 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03943_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03943 (fullRecordGapValue03943 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03943_not_prime : ¬(recordGapCenter + 16200).Prime := by
  rw [fullRecordGapTerm03943_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03943, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03943_fast_pow_mod_ne_one

def fullRecordGapValue03944 : Nat := fullRecordGapCenterValue + 16632

theorem fullRecordGapTerm03944_eq_value :
    recordGapCenter + 16632 = fullRecordGapValue03944 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03944_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03944 (fullRecordGapValue03944 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03944_not_prime : ¬(recordGapCenter + 16632).Prime := by
  rw [fullRecordGapTerm03944_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03944, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03944_fast_pow_mod_ne_one

def fullRecordGapValue03945 : Nat := fullRecordGapCenterValue + 16800

theorem fullRecordGapTerm03945_eq_value :
    recordGapCenter + 16800 = fullRecordGapValue03945 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03945_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03945 (fullRecordGapValue03945 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03945_not_prime : ¬(recordGapCenter + 16800).Prime := by
  rw [fullRecordGapTerm03945_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03945, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03945_fast_pow_mod_ne_one

def fullRecordGapValue03946 : Nat := fullRecordGapCenterValue + 16940

theorem fullRecordGapTerm03946_eq_value :
    recordGapCenter + 16940 = fullRecordGapValue03946 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03946_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03946 (fullRecordGapValue03946 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03946_not_prime : ¬(recordGapCenter + 16940).Prime := by
  rw [fullRecordGapTerm03946_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03946, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03946_fast_pow_mod_ne_one

def fullRecordGapValue03947 : Nat := fullRecordGapCenterValue + 17150

theorem fullRecordGapTerm03947_eq_value :
    recordGapCenter + 17150 = fullRecordGapValue03947 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03947_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03947 (fullRecordGapValue03947 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03947_not_prime : ¬(recordGapCenter + 17150).Prime := by
  rw [fullRecordGapTerm03947_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03947, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03947_fast_pow_mod_ne_one

def fullRecordGapValue03948 : Nat := fullRecordGapCenterValue + 17280

theorem fullRecordGapTerm03948_eq_value :
    recordGapCenter + 17280 = fullRecordGapValue03948 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03948_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03948 (fullRecordGapValue03948 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03948_not_prime : ¬(recordGapCenter + 17280).Prime := by
  rw [fullRecordGapTerm03948_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03948, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03948_fast_pow_mod_ne_one

def fullRecordGapValue03949 : Nat := fullRecordGapCenterValue + 17496

theorem fullRecordGapTerm03949_eq_value :
    recordGapCenter + 17496 = fullRecordGapValue03949 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03949_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03949 (fullRecordGapValue03949 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03949_not_prime : ¬(recordGapCenter + 17496).Prime := by
  rw [fullRecordGapTerm03949_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03949, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03949_fast_pow_mod_ne_one

def fullRecordGapValue03950 : Nat := fullRecordGapCenterValue + 17600

theorem fullRecordGapTerm03950_eq_value :
    recordGapCenter + 17600 = fullRecordGapValue03950 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03950_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03950 (fullRecordGapValue03950 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03950_not_prime : ¬(recordGapCenter + 17600).Prime := by
  rw [fullRecordGapTerm03950_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03950, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03950_fast_pow_mod_ne_one

def fullRecordGapValue03951 : Nat := fullRecordGapCenterValue + 17820

theorem fullRecordGapTerm03951_eq_value :
    recordGapCenter + 17820 = fullRecordGapValue03951 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03951_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03951 (fullRecordGapValue03951 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03951_not_prime : ¬(recordGapCenter + 17820).Prime := by
  rw [fullRecordGapTerm03951_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03951, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03951_fast_pow_mod_ne_one

def fullRecordGapValue03952 : Nat := fullRecordGapCenterValue + 18000

theorem fullRecordGapTerm03952_eq_value :
    recordGapCenter + 18000 = fullRecordGapValue03952 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03952_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03952 (fullRecordGapValue03952 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03952_not_prime : ¬(recordGapCenter + 18000).Prime := by
  rw [fullRecordGapTerm03952_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03952, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03952_fast_pow_mod_ne_one

def fullRecordGapValue03953 : Nat := fullRecordGapCenterValue + 18480

theorem fullRecordGapTerm03953_eq_value :
    recordGapCenter + 18480 = fullRecordGapValue03953 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03953_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03953 (fullRecordGapValue03953 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03953_not_prime : ¬(recordGapCenter + 18480).Prime := by
  rw [fullRecordGapTerm03953_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03953, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03953_fast_pow_mod_ne_one

def fullRecordGapValue03954 : Nat := fullRecordGapCenterValue + 18816

theorem fullRecordGapTerm03954_eq_value :
    recordGapCenter + 18816 = fullRecordGapValue03954 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03954_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03954 (fullRecordGapValue03954 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03954_not_prime : ¬(recordGapCenter + 18816).Prime := by
  rw [fullRecordGapTerm03954_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03954, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03954_fast_pow_mod_ne_one

def fullRecordGapValue03955 : Nat := fullRecordGapCenterValue + 18900

theorem fullRecordGapTerm03955_eq_value :
    recordGapCenter + 18900 = fullRecordGapValue03955 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03955_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03955 (fullRecordGapValue03955 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03955_not_prime : ¬(recordGapCenter + 18900).Prime := by
  rw [fullRecordGapTerm03955_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03955, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03955_fast_pow_mod_ne_one

def fullRecordGapValue03956 : Nat := fullRecordGapCenterValue + 19008

theorem fullRecordGapTerm03956_eq_value :
    recordGapCenter + 19008 = fullRecordGapValue03956 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03956_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03956 (fullRecordGapValue03956 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03956_not_prime : ¬(recordGapCenter + 19008).Prime := by
  rw [fullRecordGapTerm03956_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03956, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03956_fast_pow_mod_ne_one

def fullRecordGapValue03957 : Nat := fullRecordGapCenterValue + 19440

theorem fullRecordGapTerm03957_eq_value :
    recordGapCenter + 19440 = fullRecordGapValue03957 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03957_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03957 (fullRecordGapValue03957 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03957_not_prime : ¬(recordGapCenter + 19440).Prime := by
  rw [fullRecordGapTerm03957_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03957, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03957_fast_pow_mod_ne_one

def fullRecordGapValue03958 : Nat := fullRecordGapCenterValue + 19602

theorem fullRecordGapTerm03958_eq_value :
    recordGapCenter + 19602 = fullRecordGapValue03958 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03958_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03958 (fullRecordGapValue03958 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03958_not_prime : ¬(recordGapCenter + 19602).Prime := by
  rw [fullRecordGapTerm03958_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03958, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03958_fast_pow_mod_ne_one

def fullRecordGapValue03959 : Nat := fullRecordGapCenterValue + 20480

theorem fullRecordGapTerm03959_eq_value :
    recordGapCenter + 20480 = fullRecordGapValue03959 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03959_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03959 (fullRecordGapValue03959 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03959_not_prime : ¬(recordGapCenter + 20480).Prime := by
  rw [fullRecordGapTerm03959_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03959, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03959_fast_pow_mod_ne_one

def fullRecordGapValue03960 : Nat := fullRecordGapCenterValue + 20580

theorem fullRecordGapTerm03960_eq_value :
    recordGapCenter + 20580 = fullRecordGapValue03960 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03960_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03960 (fullRecordGapValue03960 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03960_not_prime : ¬(recordGapCenter + 20580).Prime := by
  rw [fullRecordGapTerm03960_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03960, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03960_fast_pow_mod_ne_one

def fullRecordGapValue03961 : Nat := fullRecordGapCenterValue + 20736

theorem fullRecordGapTerm03961_eq_value :
    recordGapCenter + 20736 = fullRecordGapValue03961 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03961_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03961 (fullRecordGapValue03961 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03961_not_prime : ¬(recordGapCenter + 20736).Prime := by
  rw [fullRecordGapTerm03961_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03961, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03961_fast_pow_mod_ne_one

def fullRecordGapValue03962 : Nat := fullRecordGapCenterValue + 21168

theorem fullRecordGapTerm03962_eq_value :
    recordGapCenter + 21168 = fullRecordGapValue03962 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03962_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03962 (fullRecordGapValue03962 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03962_not_prime : ¬(recordGapCenter + 21168).Prime := by
  rw [fullRecordGapTerm03962_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03962, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03962_fast_pow_mod_ne_one

def fullRecordGapValue03963 : Nat := fullRecordGapCenterValue + 21560

theorem fullRecordGapTerm03963_eq_value :
    recordGapCenter + 21560 = fullRecordGapValue03963 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03963_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03963 (fullRecordGapValue03963 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03963_not_prime : ¬(recordGapCenter + 21560).Prime := by
  rw [fullRecordGapTerm03963_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03963, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03963_fast_pow_mod_ne_one

def fullRecordGapValue03964 : Nat := fullRecordGapCenterValue + 21780

theorem fullRecordGapTerm03964_eq_value :
    recordGapCenter + 21780 = fullRecordGapValue03964 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03964_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03964 (fullRecordGapValue03964 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03964_not_prime : ¬(recordGapCenter + 21780).Prime := by
  rw [fullRecordGapTerm03964_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03964, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03964_fast_pow_mod_ne_one

def fullRecordGapValue03965 : Nat := fullRecordGapCenterValue + 22176

theorem fullRecordGapTerm03965_eq_value :
    recordGapCenter + 22176 = fullRecordGapValue03965 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03965_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03965 (fullRecordGapValue03965 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03965_not_prime : ¬(recordGapCenter + 22176).Prime := by
  rw [fullRecordGapTerm03965_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03965, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03965_fast_pow_mod_ne_one

def fullRecordGapValue03966 : Nat := fullRecordGapCenterValue + 22400

theorem fullRecordGapTerm03966_eq_value :
    recordGapCenter + 22400 = fullRecordGapValue03966 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03966_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03966 (fullRecordGapValue03966 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03966_not_prime : ¬(recordGapCenter + 22400).Prime := by
  rw [fullRecordGapTerm03966_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03966, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03966_fast_pow_mod_ne_one

def fullRecordGapValue03967 : Nat := fullRecordGapCenterValue + 22500

theorem fullRecordGapTerm03967_eq_value :
    recordGapCenter + 22500 = fullRecordGapValue03967 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03967_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03967 (fullRecordGapValue03967 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03967_not_prime : ¬(recordGapCenter + 22500).Prime := by
  rw [fullRecordGapTerm03967_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03967, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03967_fast_pow_mod_ne_one

def fullRecordGapValue03968 : Nat := fullRecordGapCenterValue + 22680

theorem fullRecordGapTerm03968_eq_value :
    recordGapCenter + 22680 = fullRecordGapValue03968 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03968_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03968 (fullRecordGapValue03968 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03968_not_prime : ¬(recordGapCenter + 22680).Prime := by
  rw [fullRecordGapTerm03968_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03968, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03968_fast_pow_mod_ne_one

def fullRecordGapValue03969 : Nat := fullRecordGapCenterValue + 23040

theorem fullRecordGapTerm03969_eq_value :
    recordGapCenter + 23040 = fullRecordGapValue03969 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03969_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03969 (fullRecordGapValue03969 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03969_not_prime : ¬(recordGapCenter + 23040).Prime := by
  rw [fullRecordGapTerm03969_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03969, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03969_fast_pow_mod_ne_one

def fullRecordGapValue03970 : Nat := fullRecordGapCenterValue + 23328

theorem fullRecordGapTerm03970_eq_value :
    recordGapCenter + 23328 = fullRecordGapValue03970 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03970_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03970 (fullRecordGapValue03970 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03970_not_prime : ¬(recordGapCenter + 23328).Prime := by
  rw [fullRecordGapTerm03970_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03970, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03970_fast_pow_mod_ne_one

def fullRecordGapValue03971 : Nat := fullRecordGapCenterValue + 24000

theorem fullRecordGapTerm03971_eq_value :
    recordGapCenter + 24000 = fullRecordGapValue03971 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03971_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03971 (fullRecordGapValue03971 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03971_not_prime : ¬(recordGapCenter + 24000).Prime := by
  rw [fullRecordGapTerm03971_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03971, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03971_fast_pow_mod_ne_one

def fullRecordGapValue03972 : Nat := fullRecordGapCenterValue + 24192

theorem fullRecordGapTerm03972_eq_value :
    recordGapCenter + 24192 = fullRecordGapValue03972 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03972_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03972 (fullRecordGapValue03972 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03972_not_prime : ¬(recordGapCenter + 24192).Prime := by
  rw [fullRecordGapTerm03972_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03972, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03972_fast_pow_mod_ne_one

def fullRecordGapValue03973 : Nat := fullRecordGapCenterValue + 24300

theorem fullRecordGapTerm03973_eq_value :
    recordGapCenter + 24300 = fullRecordGapValue03973 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03973_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03973 (fullRecordGapValue03973 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03973_not_prime : ¬(recordGapCenter + 24300).Prime := by
  rw [fullRecordGapTerm03973_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03973, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03973_fast_pow_mod_ne_one

def fullRecordGapValue03974 : Nat := fullRecordGapCenterValue + 24500

theorem fullRecordGapTerm03974_eq_value :
    recordGapCenter + 24500 = fullRecordGapValue03974 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03974_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03974 (fullRecordGapValue03974 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03974_not_prime : ¬(recordGapCenter + 24500).Prime := by
  rw [fullRecordGapTerm03974_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03974, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03974_fast_pow_mod_ne_one

def fullRecordGapValue03975 : Nat := fullRecordGapCenterValue + 24696

theorem fullRecordGapTerm03975_eq_value :
    recordGapCenter + 24696 = fullRecordGapValue03975 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03975_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03975 (fullRecordGapValue03975 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03975_not_prime : ¬(recordGapCenter + 24696).Prime := by
  rw [fullRecordGapTerm03975_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03975, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03975_fast_pow_mod_ne_one

def fullRecordGapValue03976 : Nat := fullRecordGapCenterValue + 24750

theorem fullRecordGapTerm03976_eq_value :
    recordGapCenter + 24750 = fullRecordGapValue03976 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03976_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03976 (fullRecordGapValue03976 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03976_not_prime : ¬(recordGapCenter + 24750).Prime := by
  rw [fullRecordGapTerm03976_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03976, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03976_fast_pow_mod_ne_one

def fullRecordGapValue03977 : Nat := fullRecordGapCenterValue + 24948

theorem fullRecordGapTerm03977_eq_value :
    recordGapCenter + 24948 = fullRecordGapValue03977 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03977_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03977 (fullRecordGapValue03977 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03977_not_prime : ¬(recordGapCenter + 24948).Prime := by
  rw [fullRecordGapTerm03977_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03977, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03977_fast_pow_mod_ne_one

def fullRecordGapValue03978 : Nat := fullRecordGapCenterValue + 25410

theorem fullRecordGapTerm03978_eq_value :
    recordGapCenter + 25410 = fullRecordGapValue03978 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03978_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03978 (fullRecordGapValue03978 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03978_not_prime : ¬(recordGapCenter + 25410).Prime := by
  rw [fullRecordGapTerm03978_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03978, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03978_fast_pow_mod_ne_one

def fullRecordGapValue03979 : Nat := fullRecordGapCenterValue + 26250

theorem fullRecordGapTerm03979_eq_value :
    recordGapCenter + 26250 = fullRecordGapValue03979 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03979_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03979 (fullRecordGapValue03979 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03979_not_prime : ¬(recordGapCenter + 26250).Prime := by
  rw [fullRecordGapTerm03979_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03979, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03979_fast_pow_mod_ne_one

def fullRecordGapValue03980 : Nat := fullRecordGapCenterValue + 26460

theorem fullRecordGapTerm03980_eq_value :
    recordGapCenter + 26460 = fullRecordGapValue03980 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03980_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03980 (fullRecordGapValue03980 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03980_not_prime : ¬(recordGapCenter + 26460).Prime := by
  rw [fullRecordGapTerm03980_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03980, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03980_fast_pow_mod_ne_one

def fullRecordGapValue03981 : Nat := fullRecordGapCenterValue + 27440

theorem fullRecordGapTerm03981_eq_value :
    recordGapCenter + 27440 = fullRecordGapValue03981 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03981_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03981 (fullRecordGapValue03981 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03981_not_prime : ¬(recordGapCenter + 27440).Prime := by
  rw [fullRecordGapTerm03981_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03981, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03981_fast_pow_mod_ne_one

def fullRecordGapValue03982 : Nat := fullRecordGapCenterValue + 27648

theorem fullRecordGapTerm03982_eq_value :
    recordGapCenter + 27648 = fullRecordGapValue03982 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03982_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03982 (fullRecordGapValue03982 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03982_not_prime : ¬(recordGapCenter + 27648).Prime := by
  rw [fullRecordGapTerm03982_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03982, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03982_fast_pow_mod_ne_one

def fullRecordGapValue03983 : Nat := fullRecordGapCenterValue + 27720

theorem fullRecordGapTerm03983_eq_value :
    recordGapCenter + 27720 = fullRecordGapValue03983 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03983_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03983 (fullRecordGapValue03983 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03983_not_prime : ¬(recordGapCenter + 27720).Prime := by
  rw [fullRecordGapTerm03983_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03983, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03983_fast_pow_mod_ne_one

def fullRecordGapValue03984 : Nat := fullRecordGapCenterValue + 28800

theorem fullRecordGapTerm03984_eq_value :
    recordGapCenter + 28800 = fullRecordGapValue03984 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03984_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03984 (fullRecordGapValue03984 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03984_not_prime : ¬(recordGapCenter + 28800).Prime := by
  rw [fullRecordGapTerm03984_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03984, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03984_fast_pow_mod_ne_one

def fullRecordGapValue03985 : Nat := fullRecordGapCenterValue + 29160

theorem fullRecordGapTerm03985_eq_value :
    recordGapCenter + 29160 = fullRecordGapValue03985 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03985_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03985 (fullRecordGapValue03985 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03985_not_prime : ¬(recordGapCenter + 29160).Prime := by
  rw [fullRecordGapTerm03985_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03985, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03985_fast_pow_mod_ne_one

def fullRecordGapValue03986 : Nat := fullRecordGapCenterValue + 29568

theorem fullRecordGapTerm03986_eq_value :
    recordGapCenter + 29568 = fullRecordGapValue03986 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03986_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03986 (fullRecordGapValue03986 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03986_not_prime : ¬(recordGapCenter + 29568).Prime := by
  rw [fullRecordGapTerm03986_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03986, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03986_fast_pow_mod_ne_one

def fullRecordGapValue03987 : Nat := fullRecordGapCenterValue + 30240

theorem fullRecordGapTerm03987_eq_value :
    recordGapCenter + 30240 = fullRecordGapValue03987 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03987_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03987 (fullRecordGapValue03987 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03987_not_prime : ¬(recordGapCenter + 30240).Prime := by
  rw [fullRecordGapTerm03987_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03987, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03987_fast_pow_mod_ne_one

def fullRecordGapValue03988 : Nat := fullRecordGapCenterValue + 30720

theorem fullRecordGapTerm03988_eq_value :
    recordGapCenter + 30720 = fullRecordGapValue03988 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03988_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03988 (fullRecordGapValue03988 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03988_not_prime : ¬(recordGapCenter + 30720).Prime := by
  rw [fullRecordGapTerm03988_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03988, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03988_fast_pow_mod_ne_one

def fullRecordGapValue03989 : Nat := fullRecordGapCenterValue + 30800

theorem fullRecordGapTerm03989_eq_value :
    recordGapCenter + 30800 = fullRecordGapValue03989 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03989_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03989 (fullRecordGapValue03989 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03989_not_prime : ¬(recordGapCenter + 30800).Prime := by
  rw [fullRecordGapTerm03989_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03989, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03989_fast_pow_mod_ne_one

def fullRecordGapValue03990 : Nat := fullRecordGapCenterValue + 32076

theorem fullRecordGapTerm03990_eq_value :
    recordGapCenter + 32076 = fullRecordGapValue03990 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03990_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03990 (fullRecordGapValue03990 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03990_not_prime : ¬(recordGapCenter + 32076).Prime := by
  rw [fullRecordGapTerm03990_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03990, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03990_fast_pow_mod_ne_one

def fullRecordGapValue03991 : Nat := fullRecordGapCenterValue + 32340

theorem fullRecordGapTerm03991_eq_value :
    recordGapCenter + 32340 = fullRecordGapValue03991 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03991_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03991 (fullRecordGapValue03991 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03991_not_prime : ¬(recordGapCenter + 32340).Prime := by
  rw [fullRecordGapTerm03991_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03991, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03991_fast_pow_mod_ne_one

def fullRecordGapValue03992 : Nat := fullRecordGapCenterValue + 32400

theorem fullRecordGapTerm03992_eq_value :
    recordGapCenter + 32400 = fullRecordGapValue03992 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03992_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03992 (fullRecordGapValue03992 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03992_not_prime : ¬(recordGapCenter + 32400).Prime := by
  rw [fullRecordGapTerm03992_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03992, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03992_fast_pow_mod_ne_one

def fullRecordGapValue03993 : Nat := fullRecordGapCenterValue + 32670

theorem fullRecordGapTerm03993_eq_value :
    recordGapCenter + 32670 = fullRecordGapValue03993 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03993_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03993 (fullRecordGapValue03993 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03993_not_prime : ¬(recordGapCenter + 32670).Prime := by
  rw [fullRecordGapTerm03993_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03993, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03993_fast_pow_mod_ne_one

def fullRecordGapValue03994 : Nat := fullRecordGapCenterValue + 33000

theorem fullRecordGapTerm03994_eq_value :
    recordGapCenter + 33000 = fullRecordGapValue03994 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03994_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03994 (fullRecordGapValue03994 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03994_not_prime : ¬(recordGapCenter + 33000).Prime := by
  rw [fullRecordGapTerm03994_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03994, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03994_fast_pow_mod_ne_one

def fullRecordGapValue03995 : Nat := fullRecordGapCenterValue + 33600

theorem fullRecordGapTerm03995_eq_value :
    recordGapCenter + 33600 = fullRecordGapValue03995 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03995_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03995 (fullRecordGapValue03995 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03995_not_prime : ¬(recordGapCenter + 33600).Prime := by
  rw [fullRecordGapTerm03995_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03995, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03995_fast_pow_mod_ne_one

def fullRecordGapValue03996 : Nat := fullRecordGapCenterValue + 34020

theorem fullRecordGapTerm03996_eq_value :
    recordGapCenter + 34020 = fullRecordGapValue03996 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03996_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03996 (fullRecordGapValue03996 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03996_not_prime : ¬(recordGapCenter + 34020).Prime := by
  rw [fullRecordGapTerm03996_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03996, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03996_fast_pow_mod_ne_one

def fullRecordGapValue03997 : Nat := fullRecordGapCenterValue + 35000

theorem fullRecordGapTerm03997_eq_value :
    recordGapCenter + 35000 = fullRecordGapValue03997 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03997_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03997 (fullRecordGapValue03997 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03997_not_prime : ¬(recordGapCenter + 35000).Prime := by
  rw [fullRecordGapTerm03997_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03997, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03997_fast_pow_mod_ne_one

def fullRecordGapValue03998 : Nat := fullRecordGapCenterValue + 35640

theorem fullRecordGapTerm03998_eq_value :
    recordGapCenter + 35640 = fullRecordGapValue03998 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03998_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03998 (fullRecordGapValue03998 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03998_not_prime : ¬(recordGapCenter + 35640).Prime := by
  rw [fullRecordGapTerm03998_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03998, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03998_fast_pow_mod_ne_one

def fullRecordGapValue03999 : Nat := fullRecordGapCenterValue + 35840

theorem fullRecordGapTerm03999_eq_value :
    recordGapCenter + 35840 = fullRecordGapValue03999 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral03999_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue03999 (fullRecordGapValue03999 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03999_not_prime : ¬(recordGapCenter + 35840).Prime := by
  rw [fullRecordGapTerm03999_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue03999, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral03999_fast_pow_mod_ne_one

def fullRecordGapValue04000 : Nat := fullRecordGapCenterValue + 37500

theorem fullRecordGapTerm04000_eq_value :
    recordGapCenter + 37500 = fullRecordGapValue04000 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04000_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04000 (fullRecordGapValue04000 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04000_not_prime : ¬(recordGapCenter + 37500).Prime := by
  rw [fullRecordGapTerm04000_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04000, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04000_fast_pow_mod_ne_one

def fullRecordGapValue04001 : Nat := fullRecordGapCenterValue + 37632

theorem fullRecordGapTerm04001_eq_value :
    recordGapCenter + 37632 = fullRecordGapValue04001 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04001_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04001 (fullRecordGapValue04001 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04001_not_prime : ¬(recordGapCenter + 37632).Prime := by
  rw [fullRecordGapTerm04001_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04001, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04001_fast_pow_mod_ne_one

def fullRecordGapValue04002 : Nat := fullRecordGapCenterValue + 38400

theorem fullRecordGapTerm04002_eq_value :
    recordGapCenter + 38400 = fullRecordGapValue04002 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04002_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04002 (fullRecordGapValue04002 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04002_not_prime : ¬(recordGapCenter + 38400).Prime := by
  rw [fullRecordGapTerm04002_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04002, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04002_fast_pow_mod_ne_one

def fullRecordGapValue04003 : Nat := fullRecordGapCenterValue + 38880

theorem fullRecordGapTerm04003_eq_value :
    recordGapCenter + 38880 = fullRecordGapValue04003 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04003_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04003 (fullRecordGapValue04003 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04003_not_prime : ¬(recordGapCenter + 38880).Prime := by
  rw [fullRecordGapTerm04003_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04003, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04003_fast_pow_mod_ne_one

def fullRecordGapValue04004 : Nat := fullRecordGapCenterValue + 39600

theorem fullRecordGapTerm04004_eq_value :
    recordGapCenter + 39600 = fullRecordGapValue04004 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04004_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04004 (fullRecordGapValue04004 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04004_not_prime : ¬(recordGapCenter + 39600).Prime := by
  rw [fullRecordGapTerm04004_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04004, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04004_fast_pow_mod_ne_one

def fullRecordGapValue04005 : Nat := fullRecordGapCenterValue + 39690

theorem fullRecordGapTerm04005_eq_value :
    recordGapCenter + 39690 = fullRecordGapValue04005 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04005_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04005 (fullRecordGapValue04005 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04005_not_prime : ¬(recordGapCenter + 39690).Prime := by
  rw [fullRecordGapTerm04005_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04005, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04005_fast_pow_mod_ne_one

def fullRecordGapValue04006 : Nat := fullRecordGapCenterValue + 40656

theorem fullRecordGapTerm04006_eq_value :
    recordGapCenter + 40656 = fullRecordGapValue04006 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04006_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04006 (fullRecordGapValue04006 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04006_not_prime : ¬(recordGapCenter + 40656).Prime := by
  rw [fullRecordGapTerm04006_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04006, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04006_fast_pow_mod_ne_one

def fullRecordGapValue04007 : Nat := fullRecordGapCenterValue + 41472

theorem fullRecordGapTerm04007_eq_value :
    recordGapCenter + 41472 = fullRecordGapValue04007 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04007_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04007 (fullRecordGapValue04007 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04007_not_prime : ¬(recordGapCenter + 41472).Prime := by
  rw [fullRecordGapTerm04007_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04007, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04007_fast_pow_mod_ne_one

def fullRecordGapValue04008 : Nat := fullRecordGapCenterValue + 42000

theorem fullRecordGapTerm04008_eq_value :
    recordGapCenter + 42000 = fullRecordGapValue04008 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04008_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04008 (fullRecordGapValue04008 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04008_not_prime : ¬(recordGapCenter + 42000).Prime := by
  rw [fullRecordGapTerm04008_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04008, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04008_fast_pow_mod_ne_one

def fullRecordGapValue04009 : Nat := fullRecordGapCenterValue + 42336

theorem fullRecordGapTerm04009_eq_value :
    recordGapCenter + 42336 = fullRecordGapValue04009 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04009_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04009 (fullRecordGapValue04009 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04009_not_prime : ¬(recordGapCenter + 42336).Prime := by
  rw [fullRecordGapTerm04009_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04009, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04009_fast_pow_mod_ne_one

def fullRecordGapValue04010 : Nat := fullRecordGapCenterValue + 43008

theorem fullRecordGapTerm04010_eq_value :
    recordGapCenter + 43008 = fullRecordGapValue04010 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04010_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04010 (fullRecordGapValue04010 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04010_not_prime : ¬(recordGapCenter + 43008).Prime := by
  rw [fullRecordGapTerm04010_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04010, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04010_fast_pow_mod_ne_one

def fullRecordGapValue04011 : Nat := fullRecordGapCenterValue + 43200

theorem fullRecordGapTerm04011_eq_value :
    recordGapCenter + 43200 = fullRecordGapValue04011 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04011_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04011 (fullRecordGapValue04011 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04011_not_prime : ¬(recordGapCenter + 43200).Prime := by
  rw [fullRecordGapTerm04011_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04011, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04011_fast_pow_mod_ne_one

def fullRecordGapValue04012 : Nat := fullRecordGapCenterValue + 44000

theorem fullRecordGapTerm04012_eq_value :
    recordGapCenter + 44000 = fullRecordGapValue04012 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04012_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04012 (fullRecordGapValue04012 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04012_not_prime : ¬(recordGapCenter + 44000).Prime := by
  rw [fullRecordGapTerm04012_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04012, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04012_fast_pow_mod_ne_one

def fullRecordGapValue04013 : Nat := fullRecordGapCenterValue + 44352

theorem fullRecordGapTerm04013_eq_value :
    recordGapCenter + 44352 = fullRecordGapValue04013 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04013_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04013 (fullRecordGapValue04013 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04013_not_prime : ¬(recordGapCenter + 44352).Prime := by
  rw [fullRecordGapTerm04013_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04013, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04013_fast_pow_mod_ne_one

def fullRecordGapValue04014 : Nat := fullRecordGapCenterValue + 45056

theorem fullRecordGapTerm04014_eq_value :
    recordGapCenter + 45056 = fullRecordGapValue04014 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04014_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04014 (fullRecordGapValue04014 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04014_not_prime : ¬(recordGapCenter + 45056).Prime := by
  rw [fullRecordGapTerm04014_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04014, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04014_fast_pow_mod_ne_one

def fullRecordGapValue04015 : Nat := fullRecordGapCenterValue + 45276

theorem fullRecordGapTerm04015_eq_value :
    recordGapCenter + 45276 = fullRecordGapValue04015 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04015_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04015 (fullRecordGapValue04015 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04015_not_prime : ¬(recordGapCenter + 45276).Prime := by
  rw [fullRecordGapTerm04015_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04015, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04015_fast_pow_mod_ne_one

def fullRecordGapValue04016 : Nat := fullRecordGapCenterValue + 46200

theorem fullRecordGapTerm04016_eq_value :
    recordGapCenter + 46200 = fullRecordGapValue04016 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04016_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04016 (fullRecordGapValue04016 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04016_not_prime : ¬(recordGapCenter + 46200).Prime := by
  rw [fullRecordGapTerm04016_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04016, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04016_fast_pow_mod_ne_one

def fullRecordGapValue04017 : Nat := fullRecordGapCenterValue + 47040

theorem fullRecordGapTerm04017_eq_value :
    recordGapCenter + 47040 = fullRecordGapValue04017 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04017_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04017 (fullRecordGapValue04017 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04017_not_prime : ¬(recordGapCenter + 47040).Prime := by
  rw [fullRecordGapTerm04017_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04017, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04017_fast_pow_mod_ne_one

def fullRecordGapValue04018 : Nat := fullRecordGapCenterValue + 47250

theorem fullRecordGapTerm04018_eq_value :
    recordGapCenter + 47250 = fullRecordGapValue04018 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04018_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04018 (fullRecordGapValue04018 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04018_not_prime : ¬(recordGapCenter + 47250).Prime := by
  rw [fullRecordGapTerm04018_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04018, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04018_fast_pow_mod_ne_one

def fullRecordGapValue04019 : Nat := fullRecordGapCenterValue + 47432

theorem fullRecordGapTerm04019_eq_value :
    recordGapCenter + 47432 = fullRecordGapValue04019 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04019_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04019 (fullRecordGapValue04019 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04019_not_prime : ¬(recordGapCenter + 47432).Prime := by
  rw [fullRecordGapTerm04019_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04019, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04019_fast_pow_mod_ne_one

def fullRecordGapValue04020 : Nat := fullRecordGapCenterValue + 48510

theorem fullRecordGapTerm04020_eq_value :
    recordGapCenter + 48510 = fullRecordGapValue04020 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04020_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04020 (fullRecordGapValue04020 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04020_not_prime : ¬(recordGapCenter + 48510).Prime := by
  rw [fullRecordGapTerm04020_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04020, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04020_fast_pow_mod_ne_one

def fullRecordGapValue04021 : Nat := fullRecordGapCenterValue + 49896

theorem fullRecordGapTerm04021_eq_value :
    recordGapCenter + 49896 = fullRecordGapValue04021 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04021_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04021 (fullRecordGapValue04021 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04021_not_prime : ¬(recordGapCenter + 49896).Prime := by
  rw [fullRecordGapTerm04021_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04021, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04021_fast_pow_mod_ne_one

def fullRecordGapValue04022 : Nat := fullRecordGapCenterValue + 50688

theorem fullRecordGapTerm04022_eq_value :
    recordGapCenter + 50688 = fullRecordGapValue04022 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04022_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04022 (fullRecordGapValue04022 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04022_not_prime : ¬(recordGapCenter + 50688).Prime := by
  rw [fullRecordGapTerm04022_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04022, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04022_fast_pow_mod_ne_one

def fullRecordGapValue04023 : Nat := fullRecordGapCenterValue + 50820

theorem fullRecordGapTerm04023_eq_value :
    recordGapCenter + 50820 = fullRecordGapValue04023 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04023_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04023 (fullRecordGapValue04023 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04023_not_prime : ¬(recordGapCenter + 50820).Prime := by
  rw [fullRecordGapTerm04023_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04023, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04023_fast_pow_mod_ne_one

def fullRecordGapValue04024 : Nat := fullRecordGapCenterValue + 52272

theorem fullRecordGapTerm04024_eq_value :
    recordGapCenter + 52272 = fullRecordGapValue04024 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04024_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04024 (fullRecordGapValue04024 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04024_not_prime : ¬(recordGapCenter + 52272).Prime := by
  rw [fullRecordGapTerm04024_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04024, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04024_fast_pow_mod_ne_one

def fullRecordGapValue04025 : Nat := fullRecordGapCenterValue + 52500

theorem fullRecordGapTerm04025_eq_value :
    recordGapCenter + 52500 = fullRecordGapValue04025 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04025_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04025 (fullRecordGapValue04025 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04025_not_prime : ¬(recordGapCenter + 52500).Prime := by
  rw [fullRecordGapTerm04025_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04025, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04025_fast_pow_mod_ne_one

def fullRecordGapValue04026 : Nat := fullRecordGapCenterValue + 53240

theorem fullRecordGapTerm04026_eq_value :
    recordGapCenter + 53240 = fullRecordGapValue04026 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04026_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04026 (fullRecordGapValue04026 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04026_not_prime : ¬(recordGapCenter + 53240).Prime := by
  rw [fullRecordGapTerm04026_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04026, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04026_fast_pow_mod_ne_one

def fullRecordGapValue04027 : Nat := fullRecordGapCenterValue + 53760

theorem fullRecordGapTerm04027_eq_value :
    recordGapCenter + 53760 = fullRecordGapValue04027 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04027_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04027 (fullRecordGapValue04027 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04027_not_prime : ¬(recordGapCenter + 53760).Prime := by
  rw [fullRecordGapTerm04027_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04027, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04027_fast_pow_mod_ne_one

def fullRecordGapValue04028 : Nat := fullRecordGapCenterValue + 54000

theorem fullRecordGapTerm04028_eq_value :
    recordGapCenter + 54000 = fullRecordGapValue04028 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04028_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04028 (fullRecordGapValue04028 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04028_not_prime : ¬(recordGapCenter + 54000).Prime := by
  rw [fullRecordGapTerm04028_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04028, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04028_fast_pow_mod_ne_one

def fullRecordGapValue04029 : Nat := fullRecordGapCenterValue + 54432

theorem fullRecordGapTerm04029_eq_value :
    recordGapCenter + 54432 = fullRecordGapValue04029 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04029_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04029 (fullRecordGapValue04029 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04029_not_prime : ¬(recordGapCenter + 54432).Prime := by
  rw [fullRecordGapTerm04029_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04029, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04029_fast_pow_mod_ne_one

def fullRecordGapValue04030 : Nat := fullRecordGapCenterValue + 56700

theorem fullRecordGapTerm04030_eq_value :
    recordGapCenter + 56700 = fullRecordGapValue04030 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04030_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04030 (fullRecordGapValue04030 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04030_not_prime : ¬(recordGapCenter + 56700).Prime := by
  rw [fullRecordGapTerm04030_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04030, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04030_fast_pow_mod_ne_one

def fullRecordGapValue04031 : Nat := fullRecordGapCenterValue + 57600

theorem fullRecordGapTerm04031_eq_value :
    recordGapCenter + 57600 = fullRecordGapValue04031 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04031_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04031 (fullRecordGapValue04031 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04031_not_prime : ¬(recordGapCenter + 57600).Prime := by
  rw [fullRecordGapTerm04031_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04031, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04031_fast_pow_mod_ne_one

def fullRecordGapValue04032 : Nat := fullRecordGapCenterValue + 57750

theorem fullRecordGapTerm04032_eq_value :
    recordGapCenter + 57750 = fullRecordGapValue04032 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04032_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04032 (fullRecordGapValue04032 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04032_not_prime : ¬(recordGapCenter + 57750).Prime := by
  rw [fullRecordGapTerm04032_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04032, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04032_fast_pow_mod_ne_one

def fullRecordGapValue04033 : Nat := fullRecordGapCenterValue + 58320

theorem fullRecordGapTerm04033_eq_value :
    recordGapCenter + 58320 = fullRecordGapValue04033 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04033_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04033 (fullRecordGapValue04033 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04033_not_prime : ¬(recordGapCenter + 58320).Prime := by
  rw [fullRecordGapTerm04033_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04033, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04033_fast_pow_mod_ne_one

def fullRecordGapValue04034 : Nat := fullRecordGapCenterValue + 60000

theorem fullRecordGapTerm04034_eq_value :
    recordGapCenter + 60000 = fullRecordGapValue04034 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04034_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04034 (fullRecordGapValue04034 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04034_not_prime : ¬(recordGapCenter + 60000).Prime := by
  rw [fullRecordGapTerm04034_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04034, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04034_fast_pow_mod_ne_one

def fullRecordGapValue04035 : Nat := fullRecordGapCenterValue + 60750

theorem fullRecordGapTerm04035_eq_value :
    recordGapCenter + 60750 = fullRecordGapValue04035 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04035_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04035 (fullRecordGapValue04035 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04035_not_prime : ¬(recordGapCenter + 60750).Prime := by
  rw [fullRecordGapTerm04035_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04035, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04035_fast_pow_mod_ne_one

def fullRecordGapValue04036 : Nat := fullRecordGapCenterValue + 61236

theorem fullRecordGapTerm04036_eq_value :
    recordGapCenter + 61236 = fullRecordGapValue04036 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04036_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04036 (fullRecordGapValue04036 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04036_not_prime : ¬(recordGapCenter + 61236).Prime := by
  rw [fullRecordGapTerm04036_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04036, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04036_fast_pow_mod_ne_one

def fullRecordGapValue04037 : Nat := fullRecordGapCenterValue + 61250

theorem fullRecordGapTerm04037_eq_value :
    recordGapCenter + 61250 = fullRecordGapValue04037 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04037_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04037 (fullRecordGapValue04037 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04037_not_prime : ¬(recordGapCenter + 61250).Prime := by
  rw [fullRecordGapTerm04037_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04037, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04037_fast_pow_mod_ne_one

def fullRecordGapValue04038 : Nat := fullRecordGapCenterValue + 61440

theorem fullRecordGapTerm04038_eq_value :
    recordGapCenter + 61440 = fullRecordGapValue04038 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04038_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04038 (fullRecordGapValue04038 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04038_not_prime : ¬(recordGapCenter + 61440).Prime := by
  rw [fullRecordGapTerm04038_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04038, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04038_fast_pow_mod_ne_one

def fullRecordGapValue04039 : Nat := fullRecordGapCenterValue + 63000

theorem fullRecordGapTerm04039_eq_value :
    recordGapCenter + 63000 = fullRecordGapValue04039 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04039_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04039 (fullRecordGapValue04039 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04039_not_prime : ¬(recordGapCenter + 63000).Prime := by
  rw [fullRecordGapTerm04039_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04039, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04039_fast_pow_mod_ne_one

def fullRecordGapValue04040 : Nat := fullRecordGapCenterValue + 64800

theorem fullRecordGapTerm04040_eq_value :
    recordGapCenter + 64800 = fullRecordGapValue04040 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04040_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04040 (fullRecordGapValue04040 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04040_not_prime : ¬(recordGapCenter + 64800).Prime := by
  rw [fullRecordGapTerm04040_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04040, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04040_fast_pow_mod_ne_one

def fullRecordGapValue04041 : Nat := fullRecordGapCenterValue + 65856

theorem fullRecordGapTerm04041_eq_value :
    recordGapCenter + 65856 = fullRecordGapValue04041 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04041_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04041 (fullRecordGapValue04041 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04041_not_prime : ¬(recordGapCenter + 65856).Prime := by
  rw [fullRecordGapTerm04041_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04041, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04041_fast_pow_mod_ne_one

def fullRecordGapValue04042 : Nat := fullRecordGapCenterValue + 67760

theorem fullRecordGapTerm04042_eq_value :
    recordGapCenter + 67760 = fullRecordGapValue04042 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04042_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04042 (fullRecordGapValue04042 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04042_not_prime : ¬(recordGapCenter + 67760).Prime := by
  rw [fullRecordGapTerm04042_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04042, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04042_fast_pow_mod_ne_one

def fullRecordGapValue04043 : Nat := fullRecordGapCenterValue + 68600

theorem fullRecordGapTerm04043_eq_value :
    recordGapCenter + 68600 = fullRecordGapValue04043 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04043_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04043 (fullRecordGapValue04043 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04043_not_prime : ¬(recordGapCenter + 68600).Prime := by
  rw [fullRecordGapTerm04043_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04043, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04043_fast_pow_mod_ne_one

def fullRecordGapValue04044 : Nat := fullRecordGapCenterValue + 69696

theorem fullRecordGapTerm04044_eq_value :
    recordGapCenter + 69696 = fullRecordGapValue04044 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04044_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04044 (fullRecordGapValue04044 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04044_not_prime : ¬(recordGapCenter + 69696).Prime := by
  rw [fullRecordGapTerm04044_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04044, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04044_fast_pow_mod_ne_one

def fullRecordGapValue04045 : Nat := fullRecordGapCenterValue + 72000

theorem fullRecordGapTerm04045_eq_value :
    recordGapCenter + 72000 = fullRecordGapValue04045 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04045_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04045 (fullRecordGapValue04045 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04045_not_prime : ¬(recordGapCenter + 72000).Prime := by
  rw [fullRecordGapTerm04045_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04045, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04045_fast_pow_mod_ne_one

def fullRecordGapValue04046 : Nat := fullRecordGapCenterValue + 72030

theorem fullRecordGapTerm04046_eq_value :
    recordGapCenter + 72030 = fullRecordGapValue04046 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04046_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04046 (fullRecordGapValue04046 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04046_not_prime : ¬(recordGapCenter + 72030).Prime := by
  rw [fullRecordGapTerm04046_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04046, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04046_fast_pow_mod_ne_one

def fullRecordGapValue04047 : Nat := fullRecordGapCenterValue + 72600

theorem fullRecordGapTerm04047_eq_value :
    recordGapCenter + 72600 = fullRecordGapValue04047 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04047_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04047 (fullRecordGapValue04047 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04047_not_prime : ¬(recordGapCenter + 72600).Prime := by
  rw [fullRecordGapTerm04047_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04047, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04047_fast_pow_mod_ne_one

def fullRecordGapValue04048 : Nat := fullRecordGapCenterValue + 73920

theorem fullRecordGapTerm04048_eq_value :
    recordGapCenter + 73920 = fullRecordGapValue04048 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04048_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04048 (fullRecordGapValue04048 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04048_not_prime : ¬(recordGapCenter + 73920).Prime := by
  rw [fullRecordGapTerm04048_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04048, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04048_fast_pow_mod_ne_one

def fullRecordGapValue04049 : Nat := fullRecordGapCenterValue + 75000

theorem fullRecordGapTerm04049_eq_value :
    recordGapCenter + 75000 = fullRecordGapValue04049 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04049_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04049 (fullRecordGapValue04049 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04049_not_prime : ¬(recordGapCenter + 75000).Prime := by
  rw [fullRecordGapTerm04049_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04049, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04049_fast_pow_mod_ne_one

def fullRecordGapValue04050 : Nat := fullRecordGapCenterValue + 76230

theorem fullRecordGapTerm04050_eq_value :
    recordGapCenter + 76230 = fullRecordGapValue04050 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04050_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04050 (fullRecordGapValue04050 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04050_not_prime : ¬(recordGapCenter + 76230).Prime := by
  rw [fullRecordGapTerm04050_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04050, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04050_fast_pow_mod_ne_one

def fullRecordGapValue04051 : Nat := fullRecordGapCenterValue + 76800

theorem fullRecordGapTerm04051_eq_value :
    recordGapCenter + 76800 = fullRecordGapValue04051 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04051_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04051 (fullRecordGapValue04051 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04051_not_prime : ¬(recordGapCenter + 76800).Prime := by
  rw [fullRecordGapTerm04051_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04051, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04051_fast_pow_mod_ne_one

def fullRecordGapValue04052 : Nat := fullRecordGapCenterValue + 76832

theorem fullRecordGapTerm04052_eq_value :
    recordGapCenter + 76832 = fullRecordGapValue04052 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04052_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04052 (fullRecordGapValue04052 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04052_not_prime : ¬(recordGapCenter + 76832).Prime := by
  rw [fullRecordGapTerm04052_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04052, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04052_fast_pow_mod_ne_one

def fullRecordGapValue04053 : Nat := fullRecordGapCenterValue + 77000

theorem fullRecordGapTerm04053_eq_value :
    recordGapCenter + 77000 = fullRecordGapValue04053 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04053_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04053 (fullRecordGapValue04053 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04053_not_prime : ¬(recordGapCenter + 77000).Prime := by
  rw [fullRecordGapTerm04053_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04053, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04053_fast_pow_mod_ne_one

def fullRecordGapValue04054 : Nat := fullRecordGapCenterValue + 77760

theorem fullRecordGapTerm04054_eq_value :
    recordGapCenter + 77760 = fullRecordGapValue04054 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04054_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04054 (fullRecordGapValue04054 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04054_not_prime : ¬(recordGapCenter + 77760).Prime := by
  rw [fullRecordGapTerm04054_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04054, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04054_fast_pow_mod_ne_one

def fullRecordGapValue04055 : Nat := fullRecordGapCenterValue + 79200

theorem fullRecordGapTerm04055_eq_value :
    recordGapCenter + 79200 = fullRecordGapValue04055 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04055_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04055 (fullRecordGapValue04055 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04055_not_prime : ¬(recordGapCenter + 79200).Prime := by
  rw [fullRecordGapTerm04055_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04055, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04055_fast_pow_mod_ne_one

def fullRecordGapValue04056 : Nat := fullRecordGapCenterValue + 80190

theorem fullRecordGapTerm04056_eq_value :
    recordGapCenter + 80190 = fullRecordGapValue04056 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04056_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04056 (fullRecordGapValue04056 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04056_not_prime : ¬(recordGapCenter + 80190).Prime := by
  rw [fullRecordGapTerm04056_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04056, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04056_fast_pow_mod_ne_one

def fullRecordGapValue04057 : Nat := fullRecordGapCenterValue + 80850

theorem fullRecordGapTerm04057_eq_value :
    recordGapCenter + 80850 = fullRecordGapValue04057 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04057_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04057 (fullRecordGapValue04057 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04057_not_prime : ¬(recordGapCenter + 80850).Prime := by
  rw [fullRecordGapTerm04057_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04057, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04057_fast_pow_mod_ne_one

def fullRecordGapValue04058 : Nat := fullRecordGapCenterValue + 83006

theorem fullRecordGapTerm04058_eq_value :
    recordGapCenter + 83006 = fullRecordGapValue04058 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04058_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04058 (fullRecordGapValue04058 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04058_not_prime : ¬(recordGapCenter + 83006).Prime := by
  rw [fullRecordGapTerm04058_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04058, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04058_fast_pow_mod_ne_one

def fullRecordGapValue04059 : Nat := fullRecordGapCenterValue + 83160

theorem fullRecordGapTerm04059_eq_value :
    recordGapCenter + 83160 = fullRecordGapValue04059 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04059_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04059 (fullRecordGapValue04059 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04059_not_prime : ¬(recordGapCenter + 83160).Prime := by
  rw [fullRecordGapTerm04059_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04059, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04059_fast_pow_mod_ne_one

def fullRecordGapValue04060 : Nat := fullRecordGapCenterValue + 84000

theorem fullRecordGapTerm04060_eq_value :
    recordGapCenter + 84000 = fullRecordGapValue04060 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04060_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04060 (fullRecordGapValue04060 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04060_not_prime : ¬(recordGapCenter + 84000).Prime := by
  rw [fullRecordGapTerm04060_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04060, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04060_fast_pow_mod_ne_one

def fullRecordGapValue04061 : Nat := fullRecordGapCenterValue + 85536

theorem fullRecordGapTerm04061_eq_value :
    recordGapCenter + 85536 = fullRecordGapValue04061 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04061_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04061 (fullRecordGapValue04061 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04061_not_prime : ¬(recordGapCenter + 85536).Prime := by
  rw [fullRecordGapTerm04061_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04061, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04061_fast_pow_mod_ne_one

def fullRecordGapValue04062 : Nat := fullRecordGapCenterValue + 86378

theorem fullRecordGapTerm04062_eq_value :
    recordGapCenter + 86378 = fullRecordGapValue04062 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04062_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04062 (fullRecordGapValue04062 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04062_not_prime : ¬(recordGapCenter + 86378).Prime := by
  rw [fullRecordGapTerm04062_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04062, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04062_fast_pow_mod_ne_one

def fullRecordGapValue04063 : Nat := fullRecordGapCenterValue + 86402

theorem fullRecordGapTerm04063_eq_value :
    recordGapCenter + 86402 = fullRecordGapValue04063 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04063_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04063 (fullRecordGapValue04063 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04063_not_prime : ¬(recordGapCenter + 86402).Prime := by
  rw [fullRecordGapTerm04063_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04063, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04063_fast_pow_mod_ne_one

def fullRecordGapValue04064 : Nat := fullRecordGapCenterValue + 86436

theorem fullRecordGapTerm04064_eq_value :
    recordGapCenter + 86436 = fullRecordGapValue04064 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04064_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04064 (fullRecordGapValue04064 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04064_not_prime : ¬(recordGapCenter + 86436).Prime := by
  rw [fullRecordGapTerm04064_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04064, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04064_fast_pow_mod_ne_one

def fullRecordGapValue04065 : Nat := fullRecordGapCenterValue + 86822

theorem fullRecordGapTerm04065_eq_value :
    recordGapCenter + 86822 = fullRecordGapValue04065 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04065_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04065 (fullRecordGapValue04065 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04065_not_prime : ¬(recordGapCenter + 86822).Prime := by
  rw [fullRecordGapTerm04065_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04065, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04065_fast_pow_mod_ne_one

def fullRecordGapValue04066 : Nat := fullRecordGapCenterValue + 87146

theorem fullRecordGapTerm04066_eq_value :
    recordGapCenter + 87146 = fullRecordGapValue04066 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04066_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04066 (fullRecordGapValue04066 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04066_not_prime : ¬(recordGapCenter + 87146).Prime := by
  rw [fullRecordGapTerm04066_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04066, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04066_fast_pow_mod_ne_one

def fullRecordGapValue04067 : Nat := fullRecordGapCenterValue + 87318

theorem fullRecordGapTerm04067_eq_value :
    recordGapCenter + 87318 = fullRecordGapValue04067 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04067_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04067 (fullRecordGapValue04067 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04067_not_prime : ¬(recordGapCenter + 87318).Prime := by
  rw [fullRecordGapTerm04067_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04067, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04067_fast_pow_mod_ne_one

def fullRecordGapValue04068 : Nat := fullRecordGapCenterValue + 87480

theorem fullRecordGapTerm04068_eq_value :
    recordGapCenter + 87480 = fullRecordGapValue04068 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04068_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04068 (fullRecordGapValue04068 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04068_not_prime : ¬(recordGapCenter + 87480).Prime := by
  rw [fullRecordGapTerm04068_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04068, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04068_fast_pow_mod_ne_one

def fullRecordGapValue04069 : Nat := fullRecordGapCenterValue + 87500

theorem fullRecordGapTerm04069_eq_value :
    recordGapCenter + 87500 = fullRecordGapValue04069 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04069_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04069 (fullRecordGapValue04069 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04069_not_prime : ¬(recordGapCenter + 87500).Prime := by
  rw [fullRecordGapTerm04069_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04069, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04069_fast_pow_mod_ne_one

def fullRecordGapValue04070 : Nat := fullRecordGapCenterValue + 87518

theorem fullRecordGapTerm04070_eq_value :
    recordGapCenter + 87518 = fullRecordGapValue04070 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04070_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04070 (fullRecordGapValue04070 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04070_not_prime : ¬(recordGapCenter + 87518).Prime := by
  rw [fullRecordGapTerm04070_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04070, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04070_fast_pow_mod_ne_one

def fullRecordGapValue04071 : Nat := fullRecordGapCenterValue + 87566

theorem fullRecordGapTerm04071_eq_value :
    recordGapCenter + 87566 = fullRecordGapValue04071 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04071_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04071 (fullRecordGapValue04071 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04071_not_prime : ¬(recordGapCenter + 87566).Prime := by
  rw [fullRecordGapTerm04071_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04071, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04071_fast_pow_mod_ne_one

def fullRecordGapValue04072 : Nat := fullRecordGapCenterValue + 87602

theorem fullRecordGapTerm04072_eq_value :
    recordGapCenter + 87602 = fullRecordGapValue04072 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04072_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04072 (fullRecordGapValue04072 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04072_not_prime : ¬(recordGapCenter + 87602).Prime := by
  rw [fullRecordGapTerm04072_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04072, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04072_fast_pow_mod_ne_one

def fullRecordGapValue04073 : Nat := fullRecordGapCenterValue + 87782

theorem fullRecordGapTerm04073_eq_value :
    recordGapCenter + 87782 = fullRecordGapValue04073 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04073_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04073 (fullRecordGapValue04073 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04073_not_prime : ¬(recordGapCenter + 87782).Prime := by
  rw [fullRecordGapTerm04073_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04073, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04073_fast_pow_mod_ne_one

def fullRecordGapValue04074 : Nat := fullRecordGapCenterValue + 87866

theorem fullRecordGapTerm04074_eq_value :
    recordGapCenter + 87866 = fullRecordGapValue04074 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04074_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04074 (fullRecordGapValue04074 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04074_not_prime : ¬(recordGapCenter + 87866).Prime := by
  rw [fullRecordGapTerm04074_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04074, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04074_fast_pow_mod_ne_one

def fullRecordGapValue04075 : Nat := fullRecordGapCenterValue + 87938

theorem fullRecordGapTerm04075_eq_value :
    recordGapCenter + 87938 = fullRecordGapValue04075 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04075_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04075 (fullRecordGapValue04075 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04075_not_prime : ¬(recordGapCenter + 87938).Prime := by
  rw [fullRecordGapTerm04075_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04075, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04075_fast_pow_mod_ne_one

def fullRecordGapValue04076 : Nat := fullRecordGapCenterValue + 88058

theorem fullRecordGapTerm04076_eq_value :
    recordGapCenter + 88058 = fullRecordGapValue04076 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04076_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04076 (fullRecordGapValue04076 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04076_not_prime : ¬(recordGapCenter + 88058).Prime := by
  rw [fullRecordGapTerm04076_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04076, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04076_fast_pow_mod_ne_one

def fullRecordGapValue04077 : Nat := fullRecordGapCenterValue + 88082

theorem fullRecordGapTerm04077_eq_value :
    recordGapCenter + 88082 = fullRecordGapValue04077 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04077_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04077 (fullRecordGapValue04077 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04077_not_prime : ¬(recordGapCenter + 88082).Prime := by
  rw [fullRecordGapTerm04077_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04077, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04077_fast_pow_mod_ne_one

def fullRecordGapValue04078 : Nat := fullRecordGapCenterValue + 88142

theorem fullRecordGapTerm04078_eq_value :
    recordGapCenter + 88142 = fullRecordGapValue04078 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04078_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04078 (fullRecordGapValue04078 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04078_not_prime : ¬(recordGapCenter + 88142).Prime := by
  rw [fullRecordGapTerm04078_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04078, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04078_fast_pow_mod_ne_one

def fullRecordGapValue04079 : Nat := fullRecordGapCenterValue + 88200

theorem fullRecordGapTerm04079_eq_value :
    recordGapCenter + 88200 = fullRecordGapValue04079 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04079_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04079 (fullRecordGapValue04079 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04079_not_prime : ¬(recordGapCenter + 88200).Prime := by
  rw [fullRecordGapTerm04079_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04079, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04079_fast_pow_mod_ne_one

def fullRecordGapValue04080 : Nat := fullRecordGapCenterValue + 88358

theorem fullRecordGapTerm04080_eq_value :
    recordGapCenter + 88358 = fullRecordGapValue04080 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04080_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04080 (fullRecordGapValue04080 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04080_not_prime : ¬(recordGapCenter + 88358).Prime := by
  rw [fullRecordGapTerm04080_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04080, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04080_fast_pow_mod_ne_one

def fullRecordGapValue04081 : Nat := fullRecordGapCenterValue + 88406

theorem fullRecordGapTerm04081_eq_value :
    recordGapCenter + 88406 = fullRecordGapValue04081 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04081_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04081 (fullRecordGapValue04081 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04081_not_prime : ¬(recordGapCenter + 88406).Prime := by
  rw [fullRecordGapTerm04081_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04081, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04081_fast_pow_mod_ne_one

def fullRecordGapValue04082 : Nat := fullRecordGapCenterValue + 88538

theorem fullRecordGapTerm04082_eq_value :
    recordGapCenter + 88538 = fullRecordGapValue04082 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04082_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04082 (fullRecordGapValue04082 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04082_not_prime : ¬(recordGapCenter + 88538).Prime := by
  rw [fullRecordGapTerm04082_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04082, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04082_fast_pow_mod_ne_one

def fullRecordGapValue04083 : Nat := fullRecordGapCenterValue + 88742

theorem fullRecordGapTerm04083_eq_value :
    recordGapCenter + 88742 = fullRecordGapValue04083 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04083_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04083 (fullRecordGapValue04083 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04083_not_prime : ¬(recordGapCenter + 88742).Prime := by
  rw [fullRecordGapTerm04083_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04083, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04083_fast_pow_mod_ne_one

def fullRecordGapValue04084 : Nat := fullRecordGapCenterValue + 89066

theorem fullRecordGapTerm04084_eq_value :
    recordGapCenter + 89066 = fullRecordGapValue04084 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04084_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04084 (fullRecordGapValue04084 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04084_not_prime : ¬(recordGapCenter + 89066).Prime := by
  rw [fullRecordGapTerm04084_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04084, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04084_fast_pow_mod_ne_one

def fullRecordGapValue04085 : Nat := fullRecordGapCenterValue + 89282

theorem fullRecordGapTerm04085_eq_value :
    recordGapCenter + 89282 = fullRecordGapValue04085 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04085_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04085 (fullRecordGapValue04085 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04085_not_prime : ¬(recordGapCenter + 89282).Prime := by
  rw [fullRecordGapTerm04085_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04085, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04085_fast_pow_mod_ne_one

def fullRecordGapValue04086 : Nat := fullRecordGapCenterValue + 89678

theorem fullRecordGapTerm04086_eq_value :
    recordGapCenter + 89678 = fullRecordGapValue04086 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04086_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04086 (fullRecordGapValue04086 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04086_not_prime : ¬(recordGapCenter + 89678).Prime := by
  rw [fullRecordGapTerm04086_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04086, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04086_fast_pow_mod_ne_one

def fullRecordGapValue04087 : Nat := fullRecordGapCenterValue + 89918

theorem fullRecordGapTerm04087_eq_value :
    recordGapCenter + 89918 = fullRecordGapValue04087 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04087_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04087 (fullRecordGapValue04087 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04087_not_prime : ¬(recordGapCenter + 89918).Prime := by
  rw [fullRecordGapTerm04087_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04087, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04087_fast_pow_mod_ne_one

def fullRecordGapValue04088 : Nat := fullRecordGapCenterValue + 89966

theorem fullRecordGapTerm04088_eq_value :
    recordGapCenter + 89966 = fullRecordGapValue04088 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04088_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04088 (fullRecordGapValue04088 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04088_not_prime : ¬(recordGapCenter + 89966).Prime := by
  rw [fullRecordGapTerm04088_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04088, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04088_fast_pow_mod_ne_one

def fullRecordGapValue04089 : Nat := fullRecordGapCenterValue + 90638

theorem fullRecordGapTerm04089_eq_value :
    recordGapCenter + 90638 = fullRecordGapValue04089 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04089_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04089 (fullRecordGapValue04089 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04089_not_prime : ¬(recordGapCenter + 90638).Prime := by
  rw [fullRecordGapTerm04089_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04089, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04089_fast_pow_mod_ne_one

def fullRecordGapValue04090 : Nat := fullRecordGapCenterValue + 90720

theorem fullRecordGapTerm04090_eq_value :
    recordGapCenter + 90720 = fullRecordGapValue04090 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04090_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04090 (fullRecordGapValue04090 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04090_not_prime : ¬(recordGapCenter + 90720).Prime := by
  rw [fullRecordGapTerm04090_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04090, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04090_fast_pow_mod_ne_one

def fullRecordGapValue04091 : Nat := fullRecordGapCenterValue + 90722

theorem fullRecordGapTerm04091_eq_value :
    recordGapCenter + 90722 = fullRecordGapValue04091 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04091_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04091 (fullRecordGapValue04091 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04091_not_prime : ¬(recordGapCenter + 90722).Prime := by
  rw [fullRecordGapTerm04091_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04091, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04091_fast_pow_mod_ne_one

def fullRecordGapValue04092 : Nat := fullRecordGapCenterValue + 91046

theorem fullRecordGapTerm04092_eq_value :
    recordGapCenter + 91046 = fullRecordGapValue04092 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04092_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04092 (fullRecordGapValue04092 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04092_not_prime : ¬(recordGapCenter + 91046).Prime := by
  rw [fullRecordGapTerm04092_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04092, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04092_fast_pow_mod_ne_one

def fullRecordGapValue04093 : Nat := fullRecordGapCenterValue + 91082

theorem fullRecordGapTerm04093_eq_value :
    recordGapCenter + 91082 = fullRecordGapValue04093 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04093_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04093 (fullRecordGapValue04093 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04093_not_prime : ¬(recordGapCenter + 91082).Prime := by
  rw [fullRecordGapTerm04093_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04093, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04093_fast_pow_mod_ne_one

def fullRecordGapValue04094 : Nat := fullRecordGapCenterValue + 91106

theorem fullRecordGapTerm04094_eq_value :
    recordGapCenter + 91106 = fullRecordGapValue04094 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04094_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04094 (fullRecordGapValue04094 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04094_not_prime : ¬(recordGapCenter + 91106).Prime := by
  rw [fullRecordGapTerm04094_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04094, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04094_fast_pow_mod_ne_one

def fullRecordGapValue04095 : Nat := fullRecordGapCenterValue + 91476

theorem fullRecordGapTerm04095_eq_value :
    recordGapCenter + 91476 = fullRecordGapValue04095 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04095_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04095 (fullRecordGapValue04095 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04095_not_prime : ¬(recordGapCenter + 91476).Prime := by
  rw [fullRecordGapTerm04095_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04095, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04095_fast_pow_mod_ne_one

def fullRecordGapValue04096 : Nat := fullRecordGapCenterValue + 91502

theorem fullRecordGapTerm04096_eq_value :
    recordGapCenter + 91502 = fullRecordGapValue04096 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04096_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04096 (fullRecordGapValue04096 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04096_not_prime : ¬(recordGapCenter + 91502).Prime := by
  rw [fullRecordGapTerm04096_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04096, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04096_fast_pow_mod_ne_one

end PrimeFactorUnimodality
