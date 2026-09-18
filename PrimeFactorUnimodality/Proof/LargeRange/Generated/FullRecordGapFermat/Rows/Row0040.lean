import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue09985 : Nat := fullRecordGapCenterValue + 600308

theorem fullRecordGapTerm09985_eq_value :
    recordGapCenter + 600308 = fullRecordGapValue09985 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09985_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09985 (fullRecordGapValue09985 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09985_not_prime : ¬(recordGapCenter + 600308).Prime := by
  rw [fullRecordGapTerm09985_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09985, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09985_fast_pow_mod_ne_one

def fullRecordGapValue09986 : Nat := fullRecordGapCenterValue + 600342

theorem fullRecordGapTerm09986_eq_value :
    recordGapCenter + 600342 = fullRecordGapValue09986 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09986_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09986 (fullRecordGapValue09986 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09986_not_prime : ¬(recordGapCenter + 600342).Prime := by
  rw [fullRecordGapTerm09986_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09986, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09986_fast_pow_mod_ne_one

def fullRecordGapValue09987 : Nat := fullRecordGapCenterValue + 600356

theorem fullRecordGapTerm09987_eq_value :
    recordGapCenter + 600356 = fullRecordGapValue09987 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09987_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09987 (fullRecordGapValue09987 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09987_not_prime : ¬(recordGapCenter + 600356).Prime := by
  rw [fullRecordGapTerm09987_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09987, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09987_fast_pow_mod_ne_one

def fullRecordGapValue09988 : Nat := fullRecordGapCenterValue + 600686

theorem fullRecordGapTerm09988_eq_value :
    recordGapCenter + 600686 = fullRecordGapValue09988 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09988_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09988 (fullRecordGapValue09988 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09988_not_prime : ¬(recordGapCenter + 600686).Prime := by
  rw [fullRecordGapTerm09988_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09988, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09988_fast_pow_mod_ne_one

def fullRecordGapValue09989 : Nat := fullRecordGapCenterValue + 600890

theorem fullRecordGapTerm09989_eq_value :
    recordGapCenter + 600890 = fullRecordGapValue09989 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09989_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09989 (fullRecordGapValue09989 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09989_not_prime : ¬(recordGapCenter + 600890).Prime := by
  rw [fullRecordGapTerm09989_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09989, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09989_fast_pow_mod_ne_one

def fullRecordGapValue09990 : Nat := fullRecordGapCenterValue + 601022

theorem fullRecordGapTerm09990_eq_value :
    recordGapCenter + 601022 = fullRecordGapValue09990 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09990_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09990 (fullRecordGapValue09990 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09990_not_prime : ¬(recordGapCenter + 601022).Prime := by
  rw [fullRecordGapTerm09990_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09990, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09990_fast_pow_mod_ne_one

def fullRecordGapValue09991 : Nat := fullRecordGapCenterValue + 601070

theorem fullRecordGapTerm09991_eq_value :
    recordGapCenter + 601070 = fullRecordGapValue09991 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09991_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09991 (fullRecordGapValue09991 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09991_not_prime : ¬(recordGapCenter + 601070).Prime := by
  rw [fullRecordGapTerm09991_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09991, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09991_fast_pow_mod_ne_one

def fullRecordGapValue09992 : Nat := fullRecordGapCenterValue + 601098

theorem fullRecordGapTerm09992_eq_value :
    recordGapCenter + 601098 = fullRecordGapValue09992 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09992_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09992 (fullRecordGapValue09992 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09992_not_prime : ¬(recordGapCenter + 601098).Prime := by
  rw [fullRecordGapTerm09992_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09992, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09992_fast_pow_mod_ne_one

def fullRecordGapValue09993 : Nat := fullRecordGapCenterValue + 601316

theorem fullRecordGapTerm09993_eq_value :
    recordGapCenter + 601316 = fullRecordGapValue09993 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09993_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09993 (fullRecordGapValue09993 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09993_not_prime : ¬(recordGapCenter + 601316).Prime := by
  rw [fullRecordGapTerm09993_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09993, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09993_fast_pow_mod_ne_one

def fullRecordGapValue09994 : Nat := fullRecordGapCenterValue + 601422

theorem fullRecordGapTerm09994_eq_value :
    recordGapCenter + 601422 = fullRecordGapValue09994 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09994_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09994 (fullRecordGapValue09994 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09994_not_prime : ¬(recordGapCenter + 601422).Prime := by
  rw [fullRecordGapTerm09994_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09994, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09994_fast_pow_mod_ne_one

def fullRecordGapValue09995 : Nat := fullRecordGapCenterValue + 601428

theorem fullRecordGapTerm09995_eq_value :
    recordGapCenter + 601428 = fullRecordGapValue09995 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09995_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09995 (fullRecordGapValue09995 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09995_not_prime : ¬(recordGapCenter + 601428).Prime := by
  rw [fullRecordGapTerm09995_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09995, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09995_fast_pow_mod_ne_one

def fullRecordGapValue09996 : Nat := fullRecordGapCenterValue + 601508

theorem fullRecordGapTerm09996_eq_value :
    recordGapCenter + 601508 = fullRecordGapValue09996 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09996_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09996 (fullRecordGapValue09996 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09996_not_prime : ¬(recordGapCenter + 601508).Prime := by
  rw [fullRecordGapTerm09996_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09996, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09996_fast_pow_mod_ne_one

def fullRecordGapValue09997 : Nat := fullRecordGapCenterValue + 601532

theorem fullRecordGapTerm09997_eq_value :
    recordGapCenter + 601532 = fullRecordGapValue09997 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09997_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09997 (fullRecordGapValue09997 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09997_not_prime : ¬(recordGapCenter + 601532).Prime := by
  rw [fullRecordGapTerm09997_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09997, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09997_fast_pow_mod_ne_one

def fullRecordGapValue09998 : Nat := fullRecordGapCenterValue + 601610

theorem fullRecordGapTerm09998_eq_value :
    recordGapCenter + 601610 = fullRecordGapValue09998 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09998_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09998 (fullRecordGapValue09998 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09998_not_prime : ¬(recordGapCenter + 601610).Prime := by
  rw [fullRecordGapTerm09998_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09998, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09998_fast_pow_mod_ne_one

def fullRecordGapValue09999 : Nat := fullRecordGapCenterValue + 601688

theorem fullRecordGapTerm09999_eq_value :
    recordGapCenter + 601688 = fullRecordGapValue09999 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral09999_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue09999 (fullRecordGapValue09999 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09999_not_prime : ¬(recordGapCenter + 601688).Prime := by
  rw [fullRecordGapTerm09999_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue09999, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral09999_fast_pow_mod_ne_one

def fullRecordGapValue10000 : Nat := fullRecordGapCenterValue + 601736

theorem fullRecordGapTerm10000_eq_value :
    recordGapCenter + 601736 = fullRecordGapValue10000 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10000_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10000 (fullRecordGapValue10000 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10000_not_prime : ¬(recordGapCenter + 601736).Prime := by
  rw [fullRecordGapTerm10000_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10000, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10000_fast_pow_mod_ne_one

def fullRecordGapValue10001 : Nat := fullRecordGapCenterValue + 601746

theorem fullRecordGapTerm10001_eq_value :
    recordGapCenter + 601746 = fullRecordGapValue10001 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10001_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10001 (fullRecordGapValue10001 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10001_not_prime : ¬(recordGapCenter + 601746).Prime := by
  rw [fullRecordGapTerm10001_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10001, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10001_fast_pow_mod_ne_one

def fullRecordGapValue10002 : Nat := fullRecordGapCenterValue + 601862

theorem fullRecordGapTerm10002_eq_value :
    recordGapCenter + 601862 = fullRecordGapValue10002 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10002_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10002 (fullRecordGapValue10002 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10002_not_prime : ¬(recordGapCenter + 601862).Prime := by
  rw [fullRecordGapTerm10002_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10002, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10002_fast_pow_mod_ne_one

def fullRecordGapValue10003 : Nat := fullRecordGapCenterValue + 602012

theorem fullRecordGapTerm10003_eq_value :
    recordGapCenter + 602012 = fullRecordGapValue10003 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10003_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10003 (fullRecordGapValue10003 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10003_not_prime : ¬(recordGapCenter + 602012).Prime := by
  rw [fullRecordGapTerm10003_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10003, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10003_fast_pow_mod_ne_one

def fullRecordGapValue10004 : Nat := fullRecordGapCenterValue + 602058

theorem fullRecordGapTerm10004_eq_value :
    recordGapCenter + 602058 = fullRecordGapValue10004 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10004_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10004 (fullRecordGapValue10004 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10004_not_prime : ¬(recordGapCenter + 602058).Prime := by
  rw [fullRecordGapTerm10004_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10004, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10004_fast_pow_mod_ne_one

def fullRecordGapValue10005 : Nat := fullRecordGapCenterValue + 602078

theorem fullRecordGapTerm10005_eq_value :
    recordGapCenter + 602078 = fullRecordGapValue10005 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10005_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10005 (fullRecordGapValue10005 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10005_not_prime : ¬(recordGapCenter + 602078).Prime := by
  rw [fullRecordGapTerm10005_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10005, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10005_fast_pow_mod_ne_one

def fullRecordGapValue10006 : Nat := fullRecordGapCenterValue + 602102

theorem fullRecordGapTerm10006_eq_value :
    recordGapCenter + 602102 = fullRecordGapValue10006 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10006_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10006 (fullRecordGapValue10006 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10006_not_prime : ¬(recordGapCenter + 602102).Prime := by
  rw [fullRecordGapTerm10006_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10006, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10006_fast_pow_mod_ne_one

def fullRecordGapValue10007 : Nat := fullRecordGapCenterValue + 602142

theorem fullRecordGapTerm10007_eq_value :
    recordGapCenter + 602142 = fullRecordGapValue10007 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10007_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10007 (fullRecordGapValue10007 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10007_not_prime : ¬(recordGapCenter + 602142).Prime := by
  rw [fullRecordGapTerm10007_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10007, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10007_fast_pow_mod_ne_one

def fullRecordGapValue10008 : Nat := fullRecordGapCenterValue + 602306

theorem fullRecordGapTerm10008_eq_value :
    recordGapCenter + 602306 = fullRecordGapValue10008 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10008_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10008 (fullRecordGapValue10008 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10008_not_prime : ¬(recordGapCenter + 602306).Prime := by
  rw [fullRecordGapTerm10008_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10008, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10008_fast_pow_mod_ne_one

def fullRecordGapValue10009 : Nat := fullRecordGapCenterValue + 602348

theorem fullRecordGapTerm10009_eq_value :
    recordGapCenter + 602348 = fullRecordGapValue10009 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10009_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10009 (fullRecordGapValue10009 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10009_not_prime : ¬(recordGapCenter + 602348).Prime := by
  rw [fullRecordGapTerm10009_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10009, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10009_fast_pow_mod_ne_one

def fullRecordGapValue10010 : Nat := fullRecordGapCenterValue + 602418

theorem fullRecordGapTerm10010_eq_value :
    recordGapCenter + 602418 = fullRecordGapValue10010 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10010_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10010 (fullRecordGapValue10010 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10010_not_prime : ¬(recordGapCenter + 602418).Prime := by
  rw [fullRecordGapTerm10010_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10010, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10010_fast_pow_mod_ne_one

def fullRecordGapValue10011 : Nat := fullRecordGapCenterValue + 602570

theorem fullRecordGapTerm10011_eq_value :
    recordGapCenter + 602570 = fullRecordGapValue10011 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10011_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10011 (fullRecordGapValue10011 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10011_not_prime : ¬(recordGapCenter + 602570).Prime := by
  rw [fullRecordGapTerm10011_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10011, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10011_fast_pow_mod_ne_one

def fullRecordGapValue10012 : Nat := fullRecordGapCenterValue + 602666

theorem fullRecordGapTerm10012_eq_value :
    recordGapCenter + 602666 = fullRecordGapValue10012 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10012_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10012 (fullRecordGapValue10012 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10012_not_prime : ¬(recordGapCenter + 602666).Prime := by
  rw [fullRecordGapTerm10012_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10012, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10012_fast_pow_mod_ne_one

def fullRecordGapValue10013 : Nat := fullRecordGapCenterValue + 602726

theorem fullRecordGapTerm10013_eq_value :
    recordGapCenter + 602726 = fullRecordGapValue10013 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10013_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10013 (fullRecordGapValue10013 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10013_not_prime : ¬(recordGapCenter + 602726).Prime := by
  rw [fullRecordGapTerm10013_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10013, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10013_fast_pow_mod_ne_one

def fullRecordGapValue10014 : Nat := fullRecordGapCenterValue + 602772

theorem fullRecordGapTerm10014_eq_value :
    recordGapCenter + 602772 = fullRecordGapValue10014 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10014_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10014 (fullRecordGapValue10014 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10014_not_prime : ¬(recordGapCenter + 602772).Prime := by
  rw [fullRecordGapTerm10014_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10014, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10014_fast_pow_mod_ne_one

def fullRecordGapValue10015 : Nat := fullRecordGapCenterValue + 602858

theorem fullRecordGapTerm10015_eq_value :
    recordGapCenter + 602858 = fullRecordGapValue10015 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10015_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10015 (fullRecordGapValue10015 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10015_not_prime : ¬(recordGapCenter + 602858).Prime := by
  rw [fullRecordGapTerm10015_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10015, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10015_fast_pow_mod_ne_one

def fullRecordGapValue10016 : Nat := fullRecordGapCenterValue + 602978

theorem fullRecordGapTerm10016_eq_value :
    recordGapCenter + 602978 = fullRecordGapValue10016 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10016_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10016 (fullRecordGapValue10016 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10016_not_prime : ¬(recordGapCenter + 602978).Prime := by
  rw [fullRecordGapTerm10016_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10016, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10016_fast_pow_mod_ne_one

def fullRecordGapValue10017 : Nat := fullRecordGapCenterValue + 603062

theorem fullRecordGapTerm10017_eq_value :
    recordGapCenter + 603062 = fullRecordGapValue10017 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10017_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10017 (fullRecordGapValue10017 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10017_not_prime : ¬(recordGapCenter + 603062).Prime := by
  rw [fullRecordGapTerm10017_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10017, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10017_fast_pow_mod_ne_one

def fullRecordGapValue10018 : Nat := fullRecordGapCenterValue + 603138

theorem fullRecordGapTerm10018_eq_value :
    recordGapCenter + 603138 = fullRecordGapValue10018 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10018_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10018 (fullRecordGapValue10018 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10018_not_prime : ¬(recordGapCenter + 603138).Prime := by
  rw [fullRecordGapTerm10018_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10018, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10018_fast_pow_mod_ne_one

def fullRecordGapValue10019 : Nat := fullRecordGapCenterValue + 603188

theorem fullRecordGapTerm10019_eq_value :
    recordGapCenter + 603188 = fullRecordGapValue10019 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10019_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10019 (fullRecordGapValue10019 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10019_not_prime : ¬(recordGapCenter + 603188).Prime := by
  rw [fullRecordGapTerm10019_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10019, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10019_fast_pow_mod_ne_one

def fullRecordGapValue10020 : Nat := fullRecordGapCenterValue + 603338

theorem fullRecordGapTerm10020_eq_value :
    recordGapCenter + 603338 = fullRecordGapValue10020 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10020_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10020 (fullRecordGapValue10020 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10020_not_prime : ¬(recordGapCenter + 603338).Prime := by
  rw [fullRecordGapTerm10020_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10020, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10020_fast_pow_mod_ne_one

def fullRecordGapValue10021 : Nat := fullRecordGapCenterValue + 603362

theorem fullRecordGapTerm10021_eq_value :
    recordGapCenter + 603362 = fullRecordGapValue10021 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10021_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10021 (fullRecordGapValue10021 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10021_not_prime : ¬(recordGapCenter + 603362).Prime := by
  rw [fullRecordGapTerm10021_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10021, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10021_fast_pow_mod_ne_one

def fullRecordGapValue10022 : Nat := fullRecordGapCenterValue + 603506

theorem fullRecordGapTerm10022_eq_value :
    recordGapCenter + 603506 = fullRecordGapValue10022 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10022_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10022 (fullRecordGapValue10022 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10022_not_prime : ¬(recordGapCenter + 603506).Prime := by
  rw [fullRecordGapTerm10022_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10022, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10022_fast_pow_mod_ne_one

def fullRecordGapValue10023 : Nat := fullRecordGapCenterValue + 603530

theorem fullRecordGapTerm10023_eq_value :
    recordGapCenter + 603530 = fullRecordGapValue10023 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10023_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10023 (fullRecordGapValue10023 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10023_not_prime : ¬(recordGapCenter + 603530).Prime := by
  rw [fullRecordGapTerm10023_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10023, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10023_fast_pow_mod_ne_one

def fullRecordGapValue10024 : Nat := fullRecordGapCenterValue + 603578

theorem fullRecordGapTerm10024_eq_value :
    recordGapCenter + 603578 = fullRecordGapValue10024 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10024_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10024 (fullRecordGapValue10024 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10024_not_prime : ¬(recordGapCenter + 603578).Prime := by
  rw [fullRecordGapTerm10024_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10024, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10024_fast_pow_mod_ne_one

def fullRecordGapValue10025 : Nat := fullRecordGapCenterValue + 603680

theorem fullRecordGapTerm10025_eq_value :
    recordGapCenter + 603680 = fullRecordGapValue10025 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10025_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10025 (fullRecordGapValue10025 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10025_not_prime : ¬(recordGapCenter + 603680).Prime := by
  rw [fullRecordGapTerm10025_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10025, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10025_fast_pow_mod_ne_one

def fullRecordGapValue10026 : Nat := fullRecordGapCenterValue + 603726

theorem fullRecordGapTerm10026_eq_value :
    recordGapCenter + 603726 = fullRecordGapValue10026 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10026_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10026 (fullRecordGapValue10026 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10026_not_prime : ¬(recordGapCenter + 603726).Prime := by
  rw [fullRecordGapTerm10026_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10026, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10026_fast_pow_mod_ne_one

def fullRecordGapValue10027 : Nat := fullRecordGapCenterValue + 603836

theorem fullRecordGapTerm10027_eq_value :
    recordGapCenter + 603836 = fullRecordGapValue10027 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10027_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10027 (fullRecordGapValue10027 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10027_not_prime : ¬(recordGapCenter + 603836).Prime := by
  rw [fullRecordGapTerm10027_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10027, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10027_fast_pow_mod_ne_one

def fullRecordGapValue10028 : Nat := fullRecordGapCenterValue + 603986

theorem fullRecordGapTerm10028_eq_value :
    recordGapCenter + 603986 = fullRecordGapValue10028 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10028_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10028 (fullRecordGapValue10028 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10028_not_prime : ¬(recordGapCenter + 603986).Prime := by
  rw [fullRecordGapTerm10028_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10028, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10028_fast_pow_mod_ne_one

def fullRecordGapValue10029 : Nat := fullRecordGapCenterValue + 604052

theorem fullRecordGapTerm10029_eq_value :
    recordGapCenter + 604052 = fullRecordGapValue10029 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10029_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10029 (fullRecordGapValue10029 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10029_not_prime : ¬(recordGapCenter + 604052).Prime := by
  rw [fullRecordGapTerm10029_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10029, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10029_fast_pow_mod_ne_one

def fullRecordGapValue10030 : Nat := fullRecordGapCenterValue + 604088

theorem fullRecordGapTerm10030_eq_value :
    recordGapCenter + 604088 = fullRecordGapValue10030 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10030_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10030 (fullRecordGapValue10030 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10030_not_prime : ¬(recordGapCenter + 604088).Prime := by
  rw [fullRecordGapTerm10030_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10030, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10030_fast_pow_mod_ne_one

def fullRecordGapValue10031 : Nat := fullRecordGapCenterValue + 604286

theorem fullRecordGapTerm10031_eq_value :
    recordGapCenter + 604286 = fullRecordGapValue10031 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10031_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10031 (fullRecordGapValue10031 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10031_not_prime : ¬(recordGapCenter + 604286).Prime := by
  rw [fullRecordGapTerm10031_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10031, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10031_fast_pow_mod_ne_one

def fullRecordGapValue10032 : Nat := fullRecordGapCenterValue + 604346

theorem fullRecordGapTerm10032_eq_value :
    recordGapCenter + 604346 = fullRecordGapValue10032 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10032_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10032 (fullRecordGapValue10032 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10032_not_prime : ¬(recordGapCenter + 604346).Prime := by
  rw [fullRecordGapTerm10032_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10032, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10032_fast_pow_mod_ne_one

def fullRecordGapValue10033 : Nat := fullRecordGapCenterValue + 604356

theorem fullRecordGapTerm10033_eq_value :
    recordGapCenter + 604356 = fullRecordGapValue10033 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10033_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10033 (fullRecordGapValue10033 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10033_not_prime : ¬(recordGapCenter + 604356).Prime := by
  rw [fullRecordGapTerm10033_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10033, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10033_fast_pow_mod_ne_one

def fullRecordGapValue10034 : Nat := fullRecordGapCenterValue + 604382

theorem fullRecordGapTerm10034_eq_value :
    recordGapCenter + 604382 = fullRecordGapValue10034 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10034_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10034 (fullRecordGapValue10034 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10034_not_prime : ¬(recordGapCenter + 604382).Prime := by
  rw [fullRecordGapTerm10034_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10034, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10034_fast_pow_mod_ne_one

def fullRecordGapValue10035 : Nat := fullRecordGapCenterValue + 604398

theorem fullRecordGapTerm10035_eq_value :
    recordGapCenter + 604398 = fullRecordGapValue10035 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10035_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10035 (fullRecordGapValue10035 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10035_not_prime : ¬(recordGapCenter + 604398).Prime := by
  rw [fullRecordGapTerm10035_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10035, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10035_fast_pow_mod_ne_one

def fullRecordGapValue10036 : Nat := fullRecordGapCenterValue + 604430

theorem fullRecordGapTerm10036_eq_value :
    recordGapCenter + 604430 = fullRecordGapValue10036 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10036_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10036 (fullRecordGapValue10036 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10036_not_prime : ¬(recordGapCenter + 604430).Prime := by
  rw [fullRecordGapTerm10036_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10036, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10036_fast_pow_mod_ne_one

def fullRecordGapValue10037 : Nat := fullRecordGapCenterValue + 604478

theorem fullRecordGapTerm10037_eq_value :
    recordGapCenter + 604478 = fullRecordGapValue10037 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10037_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10037 (fullRecordGapValue10037 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10037_not_prime : ¬(recordGapCenter + 604478).Prime := by
  rw [fullRecordGapTerm10037_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10037, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10037_fast_pow_mod_ne_one

def fullRecordGapValue10038 : Nat := fullRecordGapCenterValue + 604646

theorem fullRecordGapTerm10038_eq_value :
    recordGapCenter + 604646 = fullRecordGapValue10038 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10038_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10038 (fullRecordGapValue10038 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10038_not_prime : ¬(recordGapCenter + 604646).Prime := by
  rw [fullRecordGapTerm10038_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10038, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10038_fast_pow_mod_ne_one

def fullRecordGapValue10039 : Nat := fullRecordGapCenterValue + 604658

theorem fullRecordGapTerm10039_eq_value :
    recordGapCenter + 604658 = fullRecordGapValue10039 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10039_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10039 (fullRecordGapValue10039 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10039_not_prime : ¬(recordGapCenter + 604658).Prime := by
  rw [fullRecordGapTerm10039_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10039, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10039_fast_pow_mod_ne_one

def fullRecordGapValue10040 : Nat := fullRecordGapCenterValue + 604866

theorem fullRecordGapTerm10040_eq_value :
    recordGapCenter + 604866 = fullRecordGapValue10040 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10040_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10040 (fullRecordGapValue10040 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10040_not_prime : ¬(recordGapCenter + 604866).Prime := by
  rw [fullRecordGapTerm10040_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10040, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10040_fast_pow_mod_ne_one

def fullRecordGapValue10041 : Nat := fullRecordGapCenterValue + 604938

theorem fullRecordGapTerm10041_eq_value :
    recordGapCenter + 604938 = fullRecordGapValue10041 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10041_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10041 (fullRecordGapValue10041 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10041_not_prime : ¬(recordGapCenter + 604938).Prime := by
  rw [fullRecordGapTerm10041_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10041, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10041_fast_pow_mod_ne_one

def fullRecordGapValue10042 : Nat := fullRecordGapCenterValue + 604970

theorem fullRecordGapTerm10042_eq_value :
    recordGapCenter + 604970 = fullRecordGapValue10042 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10042_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10042 (fullRecordGapValue10042 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10042_not_prime : ¬(recordGapCenter + 604970).Prime := by
  rw [fullRecordGapTerm10042_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10042, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10042_fast_pow_mod_ne_one

def fullRecordGapValue10043 : Nat := fullRecordGapCenterValue + 605052

theorem fullRecordGapTerm10043_eq_value :
    recordGapCenter + 605052 = fullRecordGapValue10043 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10043_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10043 (fullRecordGapValue10043 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10043_not_prime : ¬(recordGapCenter + 605052).Prime := by
  rw [fullRecordGapTerm10043_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10043, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10043_fast_pow_mod_ne_one

def fullRecordGapValue10044 : Nat := fullRecordGapCenterValue + 605082

theorem fullRecordGapTerm10044_eq_value :
    recordGapCenter + 605082 = fullRecordGapValue10044 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10044_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10044 (fullRecordGapValue10044 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10044_not_prime : ¬(recordGapCenter + 605082).Prime := by
  rw [fullRecordGapTerm10044_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10044, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10044_fast_pow_mod_ne_one

def fullRecordGapValue10045 : Nat := fullRecordGapCenterValue + 605090

theorem fullRecordGapTerm10045_eq_value :
    recordGapCenter + 605090 = fullRecordGapValue10045 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10045_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10045 (fullRecordGapValue10045 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10045_not_prime : ¬(recordGapCenter + 605090).Prime := by
  rw [fullRecordGapTerm10045_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10045, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10045_fast_pow_mod_ne_one

def fullRecordGapValue10046 : Nat := fullRecordGapCenterValue + 605102

theorem fullRecordGapTerm10046_eq_value :
    recordGapCenter + 605102 = fullRecordGapValue10046 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10046_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10046 (fullRecordGapValue10046 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10046_not_prime : ¬(recordGapCenter + 605102).Prime := by
  rw [fullRecordGapTerm10046_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10046, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10046_fast_pow_mod_ne_one

def fullRecordGapValue10047 : Nat := fullRecordGapCenterValue + 605126

theorem fullRecordGapTerm10047_eq_value :
    recordGapCenter + 605126 = fullRecordGapValue10047 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10047_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10047 (fullRecordGapValue10047 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10047_not_prime : ¬(recordGapCenter + 605126).Prime := by
  rw [fullRecordGapTerm10047_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10047, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10047_fast_pow_mod_ne_one

def fullRecordGapValue10048 : Nat := fullRecordGapCenterValue + 605270

theorem fullRecordGapTerm10048_eq_value :
    recordGapCenter + 605270 = fullRecordGapValue10048 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10048_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10048 (fullRecordGapValue10048 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10048_not_prime : ¬(recordGapCenter + 605270).Prime := by
  rw [fullRecordGapTerm10048_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10048, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10048_fast_pow_mod_ne_one

def fullRecordGapValue10049 : Nat := fullRecordGapCenterValue + 605508

theorem fullRecordGapTerm10049_eq_value :
    recordGapCenter + 605508 = fullRecordGapValue10049 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10049_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10049 (fullRecordGapValue10049 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10049_not_prime : ¬(recordGapCenter + 605508).Prime := by
  rw [fullRecordGapTerm10049_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10049, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10049_fast_pow_mod_ne_one

def fullRecordGapValue10050 : Nat := fullRecordGapCenterValue + 605516

theorem fullRecordGapTerm10050_eq_value :
    recordGapCenter + 605516 = fullRecordGapValue10050 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10050_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10050 (fullRecordGapValue10050 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10050_not_prime : ¬(recordGapCenter + 605516).Prime := by
  rw [fullRecordGapTerm10050_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10050, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10050_fast_pow_mod_ne_one

def fullRecordGapValue10051 : Nat := fullRecordGapCenterValue + 605532

theorem fullRecordGapTerm10051_eq_value :
    recordGapCenter + 605532 = fullRecordGapValue10051 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10051_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10051 (fullRecordGapValue10051 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10051_not_prime : ¬(recordGapCenter + 605532).Prime := by
  rw [fullRecordGapTerm10051_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10051, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10051_fast_pow_mod_ne_one

def fullRecordGapValue10052 : Nat := fullRecordGapCenterValue + 605586

theorem fullRecordGapTerm10052_eq_value :
    recordGapCenter + 605586 = fullRecordGapValue10052 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10052_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10052 (fullRecordGapValue10052 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10052_not_prime : ¬(recordGapCenter + 605586).Prime := by
  rw [fullRecordGapTerm10052_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10052, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10052_fast_pow_mod_ne_one

def fullRecordGapValue10053 : Nat := fullRecordGapCenterValue + 605732

theorem fullRecordGapTerm10053_eq_value :
    recordGapCenter + 605732 = fullRecordGapValue10053 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10053_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10053 (fullRecordGapValue10053 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10053_not_prime : ¬(recordGapCenter + 605732).Prime := by
  rw [fullRecordGapTerm10053_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10053, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10053_fast_pow_mod_ne_one

def fullRecordGapValue10054 : Nat := fullRecordGapCenterValue + 606026

theorem fullRecordGapTerm10054_eq_value :
    recordGapCenter + 606026 = fullRecordGapValue10054 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10054_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10054 (fullRecordGapValue10054 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10054_not_prime : ¬(recordGapCenter + 606026).Prime := by
  rw [fullRecordGapTerm10054_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10054, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10054_fast_pow_mod_ne_one

def fullRecordGapValue10055 : Nat := fullRecordGapCenterValue + 606068

theorem fullRecordGapTerm10055_eq_value :
    recordGapCenter + 606068 = fullRecordGapValue10055 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10055_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10055 (fullRecordGapValue10055 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10055_not_prime : ¬(recordGapCenter + 606068).Prime := by
  rw [fullRecordGapTerm10055_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10055, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10055_fast_pow_mod_ne_one

def fullRecordGapValue10056 : Nat := fullRecordGapCenterValue + 606092

theorem fullRecordGapTerm10056_eq_value :
    recordGapCenter + 606092 = fullRecordGapValue10056 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10056_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10056 (fullRecordGapValue10056 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10056_not_prime : ¬(recordGapCenter + 606092).Prime := by
  rw [fullRecordGapTerm10056_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10056, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10056_fast_pow_mod_ne_one

def fullRecordGapValue10057 : Nat := fullRecordGapCenterValue + 606098

theorem fullRecordGapTerm10057_eq_value :
    recordGapCenter + 606098 = fullRecordGapValue10057 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10057_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10057 (fullRecordGapValue10057 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10057_not_prime : ¬(recordGapCenter + 606098).Prime := by
  rw [fullRecordGapTerm10057_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10057, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10057_fast_pow_mod_ne_one

def fullRecordGapValue10058 : Nat := fullRecordGapCenterValue + 606182

theorem fullRecordGapTerm10058_eq_value :
    recordGapCenter + 606182 = fullRecordGapValue10058 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10058_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10058 (fullRecordGapValue10058 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10058_not_prime : ¬(recordGapCenter + 606182).Prime := by
  rw [fullRecordGapTerm10058_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10058, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10058_fast_pow_mod_ne_one

def fullRecordGapValue10059 : Nat := fullRecordGapCenterValue + 606278

theorem fullRecordGapTerm10059_eq_value :
    recordGapCenter + 606278 = fullRecordGapValue10059 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10059_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10059 (fullRecordGapValue10059 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10059_not_prime : ¬(recordGapCenter + 606278).Prime := by
  rw [fullRecordGapTerm10059_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10059, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10059_fast_pow_mod_ne_one

def fullRecordGapValue10060 : Nat := fullRecordGapCenterValue + 606306

theorem fullRecordGapTerm10060_eq_value :
    recordGapCenter + 606306 = fullRecordGapValue10060 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10060_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10060 (fullRecordGapValue10060 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10060_not_prime : ¬(recordGapCenter + 606306).Prime := by
  rw [fullRecordGapTerm10060_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10060, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10060_fast_pow_mod_ne_one

def fullRecordGapValue10061 : Nat := fullRecordGapCenterValue + 606468

theorem fullRecordGapTerm10061_eq_value :
    recordGapCenter + 606468 = fullRecordGapValue10061 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10061_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10061 (fullRecordGapValue10061 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10061_not_prime : ¬(recordGapCenter + 606468).Prime := by
  rw [fullRecordGapTerm10061_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10061, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10061_fast_pow_mod_ne_one

def fullRecordGapValue10062 : Nat := fullRecordGapCenterValue + 606516

theorem fullRecordGapTerm10062_eq_value :
    recordGapCenter + 606516 = fullRecordGapValue10062 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10062_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10062 (fullRecordGapValue10062 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10062_not_prime : ¬(recordGapCenter + 606516).Prime := by
  rw [fullRecordGapTerm10062_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10062, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10062_fast_pow_mod_ne_one

def fullRecordGapValue10063 : Nat := fullRecordGapCenterValue + 606566

theorem fullRecordGapTerm10063_eq_value :
    recordGapCenter + 606566 = fullRecordGapValue10063 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10063_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10063 (fullRecordGapValue10063 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10063_not_prime : ¬(recordGapCenter + 606566).Prime := by
  rw [fullRecordGapTerm10063_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10063, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10063_fast_pow_mod_ne_one

def fullRecordGapValue10064 : Nat := fullRecordGapCenterValue + 606572

theorem fullRecordGapTerm10064_eq_value :
    recordGapCenter + 606572 = fullRecordGapValue10064 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10064_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10064 (fullRecordGapValue10064 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10064_not_prime : ¬(recordGapCenter + 606572).Prime := by
  rw [fullRecordGapTerm10064_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10064, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10064_fast_pow_mod_ne_one

def fullRecordGapValue10065 : Nat := fullRecordGapCenterValue + 606642

theorem fullRecordGapTerm10065_eq_value :
    recordGapCenter + 606642 = fullRecordGapValue10065 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10065_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10065 (fullRecordGapValue10065 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10065_not_prime : ¬(recordGapCenter + 606642).Prime := by
  rw [fullRecordGapTerm10065_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10065, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10065_fast_pow_mod_ne_one

def fullRecordGapValue10066 : Nat := fullRecordGapCenterValue + 606666

theorem fullRecordGapTerm10066_eq_value :
    recordGapCenter + 606666 = fullRecordGapValue10066 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10066_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10066 (fullRecordGapValue10066 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10066_not_prime : ¬(recordGapCenter + 606666).Prime := by
  rw [fullRecordGapTerm10066_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10066, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10066_fast_pow_mod_ne_one

def fullRecordGapValue10067 : Nat := fullRecordGapCenterValue + 606692

theorem fullRecordGapTerm10067_eq_value :
    recordGapCenter + 606692 = fullRecordGapValue10067 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10067_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10067 (fullRecordGapValue10067 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10067_not_prime : ¬(recordGapCenter + 606692).Prime := by
  rw [fullRecordGapTerm10067_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10067, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10067_fast_pow_mod_ne_one

def fullRecordGapValue10068 : Nat := fullRecordGapCenterValue + 606702

theorem fullRecordGapTerm10068_eq_value :
    recordGapCenter + 606702 = fullRecordGapValue10068 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10068_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10068 (fullRecordGapValue10068 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10068_not_prime : ¬(recordGapCenter + 606702).Prime := by
  rw [fullRecordGapTerm10068_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10068, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10068_fast_pow_mod_ne_one

def fullRecordGapValue10069 : Nat := fullRecordGapCenterValue + 606926

theorem fullRecordGapTerm10069_eq_value :
    recordGapCenter + 606926 = fullRecordGapValue10069 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10069_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10069 (fullRecordGapValue10069 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10069_not_prime : ¬(recordGapCenter + 606926).Prime := by
  rw [fullRecordGapTerm10069_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10069, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10069_fast_pow_mod_ne_one

def fullRecordGapValue10070 : Nat := fullRecordGapCenterValue + 606972

theorem fullRecordGapTerm10070_eq_value :
    recordGapCenter + 606972 = fullRecordGapValue10070 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10070_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10070 (fullRecordGapValue10070 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10070_not_prime : ¬(recordGapCenter + 606972).Prime := by
  rw [fullRecordGapTerm10070_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10070, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10070_fast_pow_mod_ne_one

def fullRecordGapValue10071 : Nat := fullRecordGapCenterValue + 607038

theorem fullRecordGapTerm10071_eq_value :
    recordGapCenter + 607038 = fullRecordGapValue10071 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10071_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10071 (fullRecordGapValue10071 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10071_not_prime : ¬(recordGapCenter + 607038).Prime := by
  rw [fullRecordGapTerm10071_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10071, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10071_fast_pow_mod_ne_one

def fullRecordGapValue10072 : Nat := fullRecordGapCenterValue + 607098

theorem fullRecordGapTerm10072_eq_value :
    recordGapCenter + 607098 = fullRecordGapValue10072 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10072_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10072 (fullRecordGapValue10072 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10072_not_prime : ¬(recordGapCenter + 607098).Prime := by
  rw [fullRecordGapTerm10072_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10072, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10072_fast_pow_mod_ne_one

def fullRecordGapValue10073 : Nat := fullRecordGapCenterValue + 607142

theorem fullRecordGapTerm10073_eq_value :
    recordGapCenter + 607142 = fullRecordGapValue10073 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10073_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10073 (fullRecordGapValue10073 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10073_not_prime : ¬(recordGapCenter + 607142).Prime := by
  rw [fullRecordGapTerm10073_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10073, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10073_fast_pow_mod_ne_one

def fullRecordGapValue10074 : Nat := fullRecordGapCenterValue + 607188

theorem fullRecordGapTerm10074_eq_value :
    recordGapCenter + 607188 = fullRecordGapValue10074 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10074_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10074 (fullRecordGapValue10074 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10074_not_prime : ¬(recordGapCenter + 607188).Prime := by
  rw [fullRecordGapTerm10074_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10074, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10074_fast_pow_mod_ne_one

def fullRecordGapValue10075 : Nat := fullRecordGapCenterValue + 607190

theorem fullRecordGapTerm10075_eq_value :
    recordGapCenter + 607190 = fullRecordGapValue10075 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10075_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10075 (fullRecordGapValue10075 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10075_not_prime : ¬(recordGapCenter + 607190).Prime := by
  rw [fullRecordGapTerm10075_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10075, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10075_fast_pow_mod_ne_one

def fullRecordGapValue10076 : Nat := fullRecordGapCenterValue + 607268

theorem fullRecordGapTerm10076_eq_value :
    recordGapCenter + 607268 = fullRecordGapValue10076 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10076_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10076 (fullRecordGapValue10076 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10076_not_prime : ¬(recordGapCenter + 607268).Prime := by
  rw [fullRecordGapTerm10076_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10076, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10076_fast_pow_mod_ne_one

def fullRecordGapValue10077 : Nat := fullRecordGapCenterValue + 607358

theorem fullRecordGapTerm10077_eq_value :
    recordGapCenter + 607358 = fullRecordGapValue10077 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10077_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10077 (fullRecordGapValue10077 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10077_not_prime : ¬(recordGapCenter + 607358).Prime := by
  rw [fullRecordGapTerm10077_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10077, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10077_fast_pow_mod_ne_one

def fullRecordGapValue10078 : Nat := fullRecordGapCenterValue + 607448

theorem fullRecordGapTerm10078_eq_value :
    recordGapCenter + 607448 = fullRecordGapValue10078 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10078_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10078 (fullRecordGapValue10078 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10078_not_prime : ¬(recordGapCenter + 607448).Prime := by
  rw [fullRecordGapTerm10078_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10078, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10078_fast_pow_mod_ne_one

def fullRecordGapValue10079 : Nat := fullRecordGapCenterValue + 607496

theorem fullRecordGapTerm10079_eq_value :
    recordGapCenter + 607496 = fullRecordGapValue10079 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10079_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10079 (fullRecordGapValue10079 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10079_not_prime : ¬(recordGapCenter + 607496).Prime := by
  rw [fullRecordGapTerm10079_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10079, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10079_fast_pow_mod_ne_one

def fullRecordGapValue10080 : Nat := fullRecordGapCenterValue + 607532

theorem fullRecordGapTerm10080_eq_value :
    recordGapCenter + 607532 = fullRecordGapValue10080 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10080_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10080 (fullRecordGapValue10080 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10080_not_prime : ¬(recordGapCenter + 607532).Prime := by
  rw [fullRecordGapTerm10080_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10080, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10080_fast_pow_mod_ne_one

def fullRecordGapValue10081 : Nat := fullRecordGapCenterValue + 607686

theorem fullRecordGapTerm10081_eq_value :
    recordGapCenter + 607686 = fullRecordGapValue10081 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10081_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10081 (fullRecordGapValue10081 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10081_not_prime : ¬(recordGapCenter + 607686).Prime := by
  rw [fullRecordGapTerm10081_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10081, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10081_fast_pow_mod_ne_one

def fullRecordGapValue10082 : Nat := fullRecordGapCenterValue + 607730

theorem fullRecordGapTerm10082_eq_value :
    recordGapCenter + 607730 = fullRecordGapValue10082 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10082_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10082 (fullRecordGapValue10082 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10082_not_prime : ¬(recordGapCenter + 607730).Prime := by
  rw [fullRecordGapTerm10082_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10082, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10082_fast_pow_mod_ne_one

def fullRecordGapValue10083 : Nat := fullRecordGapCenterValue + 607748

theorem fullRecordGapTerm10083_eq_value :
    recordGapCenter + 607748 = fullRecordGapValue10083 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10083_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10083 (fullRecordGapValue10083 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10083_not_prime : ¬(recordGapCenter + 607748).Prime := by
  rw [fullRecordGapTerm10083_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10083, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10083_fast_pow_mod_ne_one

def fullRecordGapValue10084 : Nat := fullRecordGapCenterValue + 607778

theorem fullRecordGapTerm10084_eq_value :
    recordGapCenter + 607778 = fullRecordGapValue10084 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10084_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10084 (fullRecordGapValue10084 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10084_not_prime : ¬(recordGapCenter + 607778).Prime := by
  rw [fullRecordGapTerm10084_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10084, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10084_fast_pow_mod_ne_one

def fullRecordGapValue10085 : Nat := fullRecordGapCenterValue + 607862

theorem fullRecordGapTerm10085_eq_value :
    recordGapCenter + 607862 = fullRecordGapValue10085 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10085_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10085 (fullRecordGapValue10085 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10085_not_prime : ¬(recordGapCenter + 607862).Prime := by
  rw [fullRecordGapTerm10085_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10085, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10085_fast_pow_mod_ne_one

def fullRecordGapValue10086 : Nat := fullRecordGapCenterValue + 607938

theorem fullRecordGapTerm10086_eq_value :
    recordGapCenter + 607938 = fullRecordGapValue10086 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10086_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10086 (fullRecordGapValue10086 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10086_not_prime : ¬(recordGapCenter + 607938).Prime := by
  rw [fullRecordGapTerm10086_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10086, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10086_fast_pow_mod_ne_one

def fullRecordGapValue10087 : Nat := fullRecordGapCenterValue + 608046

theorem fullRecordGapTerm10087_eq_value :
    recordGapCenter + 608046 = fullRecordGapValue10087 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10087_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10087 (fullRecordGapValue10087 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10087_not_prime : ¬(recordGapCenter + 608046).Prime := by
  rw [fullRecordGapTerm10087_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10087, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10087_fast_pow_mod_ne_one

def fullRecordGapValue10088 : Nat := fullRecordGapCenterValue + 608108

theorem fullRecordGapTerm10088_eq_value :
    recordGapCenter + 608108 = fullRecordGapValue10088 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10088_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10088 (fullRecordGapValue10088 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10088_not_prime : ¬(recordGapCenter + 608108).Prime := by
  rw [fullRecordGapTerm10088_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10088, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10088_fast_pow_mod_ne_one

def fullRecordGapValue10089 : Nat := fullRecordGapCenterValue + 608126

theorem fullRecordGapTerm10089_eq_value :
    recordGapCenter + 608126 = fullRecordGapValue10089 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10089_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10089 (fullRecordGapValue10089 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10089_not_prime : ¬(recordGapCenter + 608126).Prime := by
  rw [fullRecordGapTerm10089_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10089, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10089_fast_pow_mod_ne_one

def fullRecordGapValue10090 : Nat := fullRecordGapCenterValue + 608162

theorem fullRecordGapTerm10090_eq_value :
    recordGapCenter + 608162 = fullRecordGapValue10090 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10090_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10090 (fullRecordGapValue10090 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10090_not_prime : ¬(recordGapCenter + 608162).Prime := by
  rw [fullRecordGapTerm10090_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10090, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10090_fast_pow_mod_ne_one

def fullRecordGapValue10091 : Nat := fullRecordGapCenterValue + 608298

theorem fullRecordGapTerm10091_eq_value :
    recordGapCenter + 608298 = fullRecordGapValue10091 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10091_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10091 (fullRecordGapValue10091 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10091_not_prime : ¬(recordGapCenter + 608298).Prime := by
  rw [fullRecordGapTerm10091_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10091, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10091_fast_pow_mod_ne_one

def fullRecordGapValue10092 : Nat := fullRecordGapCenterValue + 608466

theorem fullRecordGapTerm10092_eq_value :
    recordGapCenter + 608466 = fullRecordGapValue10092 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10092_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10092 (fullRecordGapValue10092 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10092_not_prime : ¬(recordGapCenter + 608466).Prime := by
  rw [fullRecordGapTerm10092_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10092, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10092_fast_pow_mod_ne_one

def fullRecordGapValue10093 : Nat := fullRecordGapCenterValue + 608606

theorem fullRecordGapTerm10093_eq_value :
    recordGapCenter + 608606 = fullRecordGapValue10093 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10093_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10093 (fullRecordGapValue10093 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10093_not_prime : ¬(recordGapCenter + 608606).Prime := by
  rw [fullRecordGapTerm10093_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10093, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10093_fast_pow_mod_ne_one

def fullRecordGapValue10094 : Nat := fullRecordGapCenterValue + 608676

theorem fullRecordGapTerm10094_eq_value :
    recordGapCenter + 608676 = fullRecordGapValue10094 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10094_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10094 (fullRecordGapValue10094 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10094_not_prime : ¬(recordGapCenter + 608676).Prime := by
  rw [fullRecordGapTerm10094_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10094, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10094_fast_pow_mod_ne_one

def fullRecordGapValue10095 : Nat := fullRecordGapCenterValue + 608732

theorem fullRecordGapTerm10095_eq_value :
    recordGapCenter + 608732 = fullRecordGapValue10095 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10095_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10095 (fullRecordGapValue10095 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10095_not_prime : ¬(recordGapCenter + 608732).Prime := by
  rw [fullRecordGapTerm10095_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10095, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10095_fast_pow_mod_ne_one

def fullRecordGapValue10096 : Nat := fullRecordGapCenterValue + 608756

theorem fullRecordGapTerm10096_eq_value :
    recordGapCenter + 608756 = fullRecordGapValue10096 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10096_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10096 (fullRecordGapValue10096 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10096_not_prime : ¬(recordGapCenter + 608756).Prime := by
  rw [fullRecordGapTerm10096_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10096, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10096_fast_pow_mod_ne_one

def fullRecordGapValue10097 : Nat := fullRecordGapCenterValue + 608858

theorem fullRecordGapTerm10097_eq_value :
    recordGapCenter + 608858 = fullRecordGapValue10097 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10097_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10097 (fullRecordGapValue10097 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10097_not_prime : ¬(recordGapCenter + 608858).Prime := by
  rw [fullRecordGapTerm10097_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10097, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10097_fast_pow_mod_ne_one

def fullRecordGapValue10098 : Nat := fullRecordGapCenterValue + 608876

theorem fullRecordGapTerm10098_eq_value :
    recordGapCenter + 608876 = fullRecordGapValue10098 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10098_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10098 (fullRecordGapValue10098 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10098_not_prime : ¬(recordGapCenter + 608876).Prime := by
  rw [fullRecordGapTerm10098_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10098, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10098_fast_pow_mod_ne_one

def fullRecordGapValue10099 : Nat := fullRecordGapCenterValue + 608898

theorem fullRecordGapTerm10099_eq_value :
    recordGapCenter + 608898 = fullRecordGapValue10099 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10099_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10099 (fullRecordGapValue10099 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10099_not_prime : ¬(recordGapCenter + 608898).Prime := by
  rw [fullRecordGapTerm10099_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10099, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10099_fast_pow_mod_ne_one

def fullRecordGapValue10100 : Nat := fullRecordGapCenterValue + 608918

theorem fullRecordGapTerm10100_eq_value :
    recordGapCenter + 608918 = fullRecordGapValue10100 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10100_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10100 (fullRecordGapValue10100 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10100_not_prime : ¬(recordGapCenter + 608918).Prime := by
  rw [fullRecordGapTerm10100_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10100, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10100_fast_pow_mod_ne_one

def fullRecordGapValue10101 : Nat := fullRecordGapCenterValue + 609036

theorem fullRecordGapTerm10101_eq_value :
    recordGapCenter + 609036 = fullRecordGapValue10101 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10101_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10101 (fullRecordGapValue10101 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10101_not_prime : ¬(recordGapCenter + 609036).Prime := by
  rw [fullRecordGapTerm10101_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10101, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10101_fast_pow_mod_ne_one

def fullRecordGapValue10102 : Nat := fullRecordGapCenterValue + 609078

theorem fullRecordGapTerm10102_eq_value :
    recordGapCenter + 609078 = fullRecordGapValue10102 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10102_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10102 (fullRecordGapValue10102 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10102_not_prime : ¬(recordGapCenter + 609078).Prime := by
  rw [fullRecordGapTerm10102_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10102, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10102_fast_pow_mod_ne_one

def fullRecordGapValue10103 : Nat := fullRecordGapCenterValue + 609170

theorem fullRecordGapTerm10103_eq_value :
    recordGapCenter + 609170 = fullRecordGapValue10103 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10103_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10103 (fullRecordGapValue10103 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10103_not_prime : ¬(recordGapCenter + 609170).Prime := by
  rw [fullRecordGapTerm10103_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10103, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10103_fast_pow_mod_ne_one

def fullRecordGapValue10104 : Nat := fullRecordGapCenterValue + 609186

theorem fullRecordGapTerm10104_eq_value :
    recordGapCenter + 609186 = fullRecordGapValue10104 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10104_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10104 (fullRecordGapValue10104 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10104_not_prime : ¬(recordGapCenter + 609186).Prime := by
  rw [fullRecordGapTerm10104_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10104, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10104_fast_pow_mod_ne_one

def fullRecordGapValue10105 : Nat := fullRecordGapCenterValue + 609276

theorem fullRecordGapTerm10105_eq_value :
    recordGapCenter + 609276 = fullRecordGapValue10105 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10105_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10105 (fullRecordGapValue10105 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10105_not_prime : ¬(recordGapCenter + 609276).Prime := by
  rw [fullRecordGapTerm10105_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10105, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10105_fast_pow_mod_ne_one

def fullRecordGapValue10106 : Nat := fullRecordGapCenterValue + 609302

theorem fullRecordGapTerm10106_eq_value :
    recordGapCenter + 609302 = fullRecordGapValue10106 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10106_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10106 (fullRecordGapValue10106 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10106_not_prime : ¬(recordGapCenter + 609302).Prime := by
  rw [fullRecordGapTerm10106_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10106, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10106_fast_pow_mod_ne_one

def fullRecordGapValue10107 : Nat := fullRecordGapCenterValue + 609326

theorem fullRecordGapTerm10107_eq_value :
    recordGapCenter + 609326 = fullRecordGapValue10107 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10107_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10107 (fullRecordGapValue10107 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10107_not_prime : ¬(recordGapCenter + 609326).Prime := by
  rw [fullRecordGapTerm10107_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10107, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10107_fast_pow_mod_ne_one

def fullRecordGapValue10108 : Nat := fullRecordGapCenterValue + 609366

theorem fullRecordGapTerm10108_eq_value :
    recordGapCenter + 609366 = fullRecordGapValue10108 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10108_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10108 (fullRecordGapValue10108 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10108_not_prime : ¬(recordGapCenter + 609366).Prime := by
  rw [fullRecordGapTerm10108_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10108, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10108_fast_pow_mod_ne_one

def fullRecordGapValue10109 : Nat := fullRecordGapCenterValue + 609438

theorem fullRecordGapTerm10109_eq_value :
    recordGapCenter + 609438 = fullRecordGapValue10109 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10109_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10109 (fullRecordGapValue10109 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10109_not_prime : ¬(recordGapCenter + 609438).Prime := by
  rw [fullRecordGapTerm10109_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10109, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10109_fast_pow_mod_ne_one

def fullRecordGapValue10110 : Nat := fullRecordGapCenterValue + 609458

theorem fullRecordGapTerm10110_eq_value :
    recordGapCenter + 609458 = fullRecordGapValue10110 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10110_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10110 (fullRecordGapValue10110 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10110_not_prime : ¬(recordGapCenter + 609458).Prime := by
  rw [fullRecordGapTerm10110_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10110, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10110_fast_pow_mod_ne_one

def fullRecordGapValue10111 : Nat := fullRecordGapCenterValue + 609486

theorem fullRecordGapTerm10111_eq_value :
    recordGapCenter + 609486 = fullRecordGapValue10111 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10111_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10111 (fullRecordGapValue10111 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10111_not_prime : ¬(recordGapCenter + 609486).Prime := by
  rw [fullRecordGapTerm10111_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10111, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10111_fast_pow_mod_ne_one

def fullRecordGapValue10112 : Nat := fullRecordGapCenterValue + 609578

theorem fullRecordGapTerm10112_eq_value :
    recordGapCenter + 609578 = fullRecordGapValue10112 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10112_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10112 (fullRecordGapValue10112 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10112_not_prime : ¬(recordGapCenter + 609578).Prime := by
  rw [fullRecordGapTerm10112_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10112, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10112_fast_pow_mod_ne_one

def fullRecordGapValue10113 : Nat := fullRecordGapCenterValue + 609666

theorem fullRecordGapTerm10113_eq_value :
    recordGapCenter + 609666 = fullRecordGapValue10113 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10113_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10113 (fullRecordGapValue10113 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10113_not_prime : ¬(recordGapCenter + 609666).Prime := by
  rw [fullRecordGapTerm10113_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10113, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10113_fast_pow_mod_ne_one

def fullRecordGapValue10114 : Nat := fullRecordGapCenterValue + 609698

theorem fullRecordGapTerm10114_eq_value :
    recordGapCenter + 609698 = fullRecordGapValue10114 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10114_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10114 (fullRecordGapValue10114 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10114_not_prime : ¬(recordGapCenter + 609698).Prime := by
  rw [fullRecordGapTerm10114_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10114, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10114_fast_pow_mod_ne_one

def fullRecordGapValue10115 : Nat := fullRecordGapCenterValue + 609758

theorem fullRecordGapTerm10115_eq_value :
    recordGapCenter + 609758 = fullRecordGapValue10115 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10115_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10115 (fullRecordGapValue10115 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10115_not_prime : ¬(recordGapCenter + 609758).Prime := by
  rw [fullRecordGapTerm10115_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10115, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10115_fast_pow_mod_ne_one

def fullRecordGapValue10116 : Nat := fullRecordGapCenterValue + 609848

theorem fullRecordGapTerm10116_eq_value :
    recordGapCenter + 609848 = fullRecordGapValue10116 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10116_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10116 (fullRecordGapValue10116 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10116_not_prime : ¬(recordGapCenter + 609848).Prime := by
  rw [fullRecordGapTerm10116_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10116, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10116_fast_pow_mod_ne_one

def fullRecordGapValue10117 : Nat := fullRecordGapCenterValue + 609852

theorem fullRecordGapTerm10117_eq_value :
    recordGapCenter + 609852 = fullRecordGapValue10117 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10117_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10117 (fullRecordGapValue10117 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10117_not_prime : ¬(recordGapCenter + 609852).Prime := by
  rw [fullRecordGapTerm10117_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10117, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10117_fast_pow_mod_ne_one

def fullRecordGapValue10118 : Nat := fullRecordGapCenterValue + 609866

theorem fullRecordGapTerm10118_eq_value :
    recordGapCenter + 609866 = fullRecordGapValue10118 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10118_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10118 (fullRecordGapValue10118 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10118_not_prime : ¬(recordGapCenter + 609866).Prime := by
  rw [fullRecordGapTerm10118_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10118, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10118_fast_pow_mod_ne_one

def fullRecordGapValue10119 : Nat := fullRecordGapCenterValue + 609962

theorem fullRecordGapTerm10119_eq_value :
    recordGapCenter + 609962 = fullRecordGapValue10119 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10119_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10119 (fullRecordGapValue10119 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10119_not_prime : ¬(recordGapCenter + 609962).Prime := by
  rw [fullRecordGapTerm10119_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10119, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10119_fast_pow_mod_ne_one

def fullRecordGapValue10120 : Nat := fullRecordGapCenterValue + 609978

theorem fullRecordGapTerm10120_eq_value :
    recordGapCenter + 609978 = fullRecordGapValue10120 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10120_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10120 (fullRecordGapValue10120 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10120_not_prime : ¬(recordGapCenter + 609978).Prime := by
  rw [fullRecordGapTerm10120_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10120, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10120_fast_pow_mod_ne_one

def fullRecordGapValue10121 : Nat := fullRecordGapCenterValue + 610068

theorem fullRecordGapTerm10121_eq_value :
    recordGapCenter + 610068 = fullRecordGapValue10121 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10121_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10121 (fullRecordGapValue10121 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10121_not_prime : ¬(recordGapCenter + 610068).Prime := by
  rw [fullRecordGapTerm10121_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10121, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10121_fast_pow_mod_ne_one

def fullRecordGapValue10122 : Nat := fullRecordGapCenterValue + 610088

theorem fullRecordGapTerm10122_eq_value :
    recordGapCenter + 610088 = fullRecordGapValue10122 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10122_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10122 (fullRecordGapValue10122 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10122_not_prime : ¬(recordGapCenter + 610088).Prime := by
  rw [fullRecordGapTerm10122_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10122, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10122_fast_pow_mod_ne_one

def fullRecordGapValue10123 : Nat := fullRecordGapCenterValue + 610106

theorem fullRecordGapTerm10123_eq_value :
    recordGapCenter + 610106 = fullRecordGapValue10123 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10123_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10123 (fullRecordGapValue10123 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10123_not_prime : ¬(recordGapCenter + 610106).Prime := by
  rw [fullRecordGapTerm10123_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10123, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10123_fast_pow_mod_ne_one

def fullRecordGapValue10124 : Nat := fullRecordGapCenterValue + 610158

theorem fullRecordGapTerm10124_eq_value :
    recordGapCenter + 610158 = fullRecordGapValue10124 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10124_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10124 (fullRecordGapValue10124 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10124_not_prime : ¬(recordGapCenter + 610158).Prime := by
  rw [fullRecordGapTerm10124_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10124, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10124_fast_pow_mod_ne_one

def fullRecordGapValue10125 : Nat := fullRecordGapCenterValue + 610206

theorem fullRecordGapTerm10125_eq_value :
    recordGapCenter + 610206 = fullRecordGapValue10125 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10125_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10125 (fullRecordGapValue10125 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10125_not_prime : ¬(recordGapCenter + 610206).Prime := by
  rw [fullRecordGapTerm10125_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10125, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10125_fast_pow_mod_ne_one

def fullRecordGapValue10126 : Nat := fullRecordGapCenterValue + 610226

theorem fullRecordGapTerm10126_eq_value :
    recordGapCenter + 610226 = fullRecordGapValue10126 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10126_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10126 (fullRecordGapValue10126 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10126_not_prime : ¬(recordGapCenter + 610226).Prime := by
  rw [fullRecordGapTerm10126_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10126, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10126_fast_pow_mod_ne_one

def fullRecordGapValue10127 : Nat := fullRecordGapCenterValue + 610262

theorem fullRecordGapTerm10127_eq_value :
    recordGapCenter + 610262 = fullRecordGapValue10127 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10127_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10127 (fullRecordGapValue10127 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10127_not_prime : ¬(recordGapCenter + 610262).Prime := by
  rw [fullRecordGapTerm10127_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10127, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10127_fast_pow_mod_ne_one

def fullRecordGapValue10128 : Nat := fullRecordGapCenterValue + 610310

theorem fullRecordGapTerm10128_eq_value :
    recordGapCenter + 610310 = fullRecordGapValue10128 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10128_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10128 (fullRecordGapValue10128 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10128_not_prime : ¬(recordGapCenter + 610310).Prime := by
  rw [fullRecordGapTerm10128_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10128, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10128_fast_pow_mod_ne_one

def fullRecordGapValue10129 : Nat := fullRecordGapCenterValue + 610338

theorem fullRecordGapTerm10129_eq_value :
    recordGapCenter + 610338 = fullRecordGapValue10129 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10129_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10129 (fullRecordGapValue10129 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10129_not_prime : ¬(recordGapCenter + 610338).Prime := by
  rw [fullRecordGapTerm10129_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10129, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10129_fast_pow_mod_ne_one

def fullRecordGapValue10130 : Nat := fullRecordGapCenterValue + 610358

theorem fullRecordGapTerm10130_eq_value :
    recordGapCenter + 610358 = fullRecordGapValue10130 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10130_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10130 (fullRecordGapValue10130 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10130_not_prime : ¬(recordGapCenter + 610358).Prime := by
  rw [fullRecordGapTerm10130_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10130, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10130_fast_pow_mod_ne_one

def fullRecordGapValue10131 : Nat := fullRecordGapCenterValue + 610422

theorem fullRecordGapTerm10131_eq_value :
    recordGapCenter + 610422 = fullRecordGapValue10131 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10131_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10131 (fullRecordGapValue10131 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10131_not_prime : ¬(recordGapCenter + 610422).Prime := by
  rw [fullRecordGapTerm10131_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10131, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10131_fast_pow_mod_ne_one

def fullRecordGapValue10132 : Nat := fullRecordGapCenterValue + 610526

theorem fullRecordGapTerm10132_eq_value :
    recordGapCenter + 610526 = fullRecordGapValue10132 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10132_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10132 (fullRecordGapValue10132 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10132_not_prime : ¬(recordGapCenter + 610526).Prime := by
  rw [fullRecordGapTerm10132_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10132, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10132_fast_pow_mod_ne_one

def fullRecordGapValue10133 : Nat := fullRecordGapCenterValue + 610556

theorem fullRecordGapTerm10133_eq_value :
    recordGapCenter + 610556 = fullRecordGapValue10133 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10133_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10133 (fullRecordGapValue10133 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10133_not_prime : ¬(recordGapCenter + 610556).Prime := by
  rw [fullRecordGapTerm10133_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10133, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10133_fast_pow_mod_ne_one

def fullRecordGapValue10134 : Nat := fullRecordGapCenterValue + 610706

theorem fullRecordGapTerm10134_eq_value :
    recordGapCenter + 610706 = fullRecordGapValue10134 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10134_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10134 (fullRecordGapValue10134 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10134_not_prime : ¬(recordGapCenter + 610706).Prime := by
  rw [fullRecordGapTerm10134_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10134, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10134_fast_pow_mod_ne_one

def fullRecordGapValue10135 : Nat := fullRecordGapCenterValue + 610778

theorem fullRecordGapTerm10135_eq_value :
    recordGapCenter + 610778 = fullRecordGapValue10135 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10135_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10135 (fullRecordGapValue10135 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10135_not_prime : ¬(recordGapCenter + 610778).Prime := by
  rw [fullRecordGapTerm10135_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10135, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10135_fast_pow_mod_ne_one

def fullRecordGapValue10136 : Nat := fullRecordGapCenterValue + 610802

theorem fullRecordGapTerm10136_eq_value :
    recordGapCenter + 610802 = fullRecordGapValue10136 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10136_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10136 (fullRecordGapValue10136 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10136_not_prime : ¬(recordGapCenter + 610802).Prime := by
  rw [fullRecordGapTerm10136_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10136, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10136_fast_pow_mod_ne_one

def fullRecordGapValue10137 : Nat := fullRecordGapCenterValue + 610862

theorem fullRecordGapTerm10137_eq_value :
    recordGapCenter + 610862 = fullRecordGapValue10137 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10137_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10137 (fullRecordGapValue10137 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10137_not_prime : ¬(recordGapCenter + 610862).Prime := by
  rw [fullRecordGapTerm10137_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10137, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10137_fast_pow_mod_ne_one

def fullRecordGapValue10138 : Nat := fullRecordGapCenterValue + 610898

theorem fullRecordGapTerm10138_eq_value :
    recordGapCenter + 610898 = fullRecordGapValue10138 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10138_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10138 (fullRecordGapValue10138 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10138_not_prime : ¬(recordGapCenter + 610898).Prime := by
  rw [fullRecordGapTerm10138_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10138, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10138_fast_pow_mod_ne_one

def fullRecordGapValue10139 : Nat := fullRecordGapCenterValue + 611012

theorem fullRecordGapTerm10139_eq_value :
    recordGapCenter + 611012 = fullRecordGapValue10139 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10139_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10139 (fullRecordGapValue10139 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10139_not_prime : ¬(recordGapCenter + 611012).Prime := by
  rw [fullRecordGapTerm10139_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10139, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10139_fast_pow_mod_ne_one

def fullRecordGapValue10140 : Nat := fullRecordGapCenterValue + 611042

theorem fullRecordGapTerm10140_eq_value :
    recordGapCenter + 611042 = fullRecordGapValue10140 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10140_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10140 (fullRecordGapValue10140 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10140_not_prime : ¬(recordGapCenter + 611042).Prime := by
  rw [fullRecordGapTerm10140_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10140, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10140_fast_pow_mod_ne_one

def fullRecordGapValue10141 : Nat := fullRecordGapCenterValue + 611066

theorem fullRecordGapTerm10141_eq_value :
    recordGapCenter + 611066 = fullRecordGapValue10141 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10141_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10141 (fullRecordGapValue10141 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10141_not_prime : ¬(recordGapCenter + 611066).Prime := by
  rw [fullRecordGapTerm10141_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10141, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10141_fast_pow_mod_ne_one

def fullRecordGapValue10142 : Nat := fullRecordGapCenterValue + 611108

theorem fullRecordGapTerm10142_eq_value :
    recordGapCenter + 611108 = fullRecordGapValue10142 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10142_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10142 (fullRecordGapValue10142 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10142_not_prime : ¬(recordGapCenter + 611108).Prime := by
  rw [fullRecordGapTerm10142_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10142, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10142_fast_pow_mod_ne_one

def fullRecordGapValue10143 : Nat := fullRecordGapCenterValue + 611126

theorem fullRecordGapTerm10143_eq_value :
    recordGapCenter + 611126 = fullRecordGapValue10143 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10143_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10143 (fullRecordGapValue10143 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10143_not_prime : ¬(recordGapCenter + 611126).Prime := by
  rw [fullRecordGapTerm10143_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10143, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10143_fast_pow_mod_ne_one

def fullRecordGapValue10144 : Nat := fullRecordGapCenterValue + 611186

theorem fullRecordGapTerm10144_eq_value :
    recordGapCenter + 611186 = fullRecordGapValue10144 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10144_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10144 (fullRecordGapValue10144 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10144_not_prime : ¬(recordGapCenter + 611186).Prime := by
  rw [fullRecordGapTerm10144_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10144, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10144_fast_pow_mod_ne_one

def fullRecordGapValue10145 : Nat := fullRecordGapCenterValue + 611210

theorem fullRecordGapTerm10145_eq_value :
    recordGapCenter + 611210 = fullRecordGapValue10145 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10145_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10145 (fullRecordGapValue10145 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10145_not_prime : ¬(recordGapCenter + 611210).Prime := by
  rw [fullRecordGapTerm10145_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10145, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10145_fast_pow_mod_ne_one

def fullRecordGapValue10146 : Nat := fullRecordGapCenterValue + 611238

theorem fullRecordGapTerm10146_eq_value :
    recordGapCenter + 611238 = fullRecordGapValue10146 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10146_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10146 (fullRecordGapValue10146 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10146_not_prime : ¬(recordGapCenter + 611238).Prime := by
  rw [fullRecordGapTerm10146_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10146, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10146_fast_pow_mod_ne_one

def fullRecordGapValue10147 : Nat := fullRecordGapCenterValue + 611346

theorem fullRecordGapTerm10147_eq_value :
    recordGapCenter + 611346 = fullRecordGapValue10147 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10147_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10147 (fullRecordGapValue10147 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10147_not_prime : ¬(recordGapCenter + 611346).Prime := by
  rw [fullRecordGapTerm10147_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10147, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10147_fast_pow_mod_ne_one

def fullRecordGapValue10148 : Nat := fullRecordGapCenterValue + 611412

theorem fullRecordGapTerm10148_eq_value :
    recordGapCenter + 611412 = fullRecordGapValue10148 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10148_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10148 (fullRecordGapValue10148 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10148_not_prime : ¬(recordGapCenter + 611412).Prime := by
  rw [fullRecordGapTerm10148_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10148, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10148_fast_pow_mod_ne_one

def fullRecordGapValue10149 : Nat := fullRecordGapCenterValue + 611438

theorem fullRecordGapTerm10149_eq_value :
    recordGapCenter + 611438 = fullRecordGapValue10149 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10149_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10149 (fullRecordGapValue10149 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10149_not_prime : ¬(recordGapCenter + 611438).Prime := by
  rw [fullRecordGapTerm10149_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10149, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10149_fast_pow_mod_ne_one

def fullRecordGapValue10150 : Nat := fullRecordGapCenterValue + 611502

theorem fullRecordGapTerm10150_eq_value :
    recordGapCenter + 611502 = fullRecordGapValue10150 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10150_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10150 (fullRecordGapValue10150 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10150_not_prime : ¬(recordGapCenter + 611502).Prime := by
  rw [fullRecordGapTerm10150_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10150, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10150_fast_pow_mod_ne_one

def fullRecordGapValue10151 : Nat := fullRecordGapCenterValue + 611628

theorem fullRecordGapTerm10151_eq_value :
    recordGapCenter + 611628 = fullRecordGapValue10151 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10151_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10151 (fullRecordGapValue10151 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10151_not_prime : ¬(recordGapCenter + 611628).Prime := by
  rw [fullRecordGapTerm10151_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10151, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10151_fast_pow_mod_ne_one

def fullRecordGapValue10152 : Nat := fullRecordGapCenterValue + 611636

theorem fullRecordGapTerm10152_eq_value :
    recordGapCenter + 611636 = fullRecordGapValue10152 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10152_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10152 (fullRecordGapValue10152 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10152_not_prime : ¬(recordGapCenter + 611636).Prime := by
  rw [fullRecordGapTerm10152_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10152, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10152_fast_pow_mod_ne_one

def fullRecordGapValue10153 : Nat := fullRecordGapCenterValue + 611642

theorem fullRecordGapTerm10153_eq_value :
    recordGapCenter + 611642 = fullRecordGapValue10153 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10153_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10153 (fullRecordGapValue10153 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10153_not_prime : ¬(recordGapCenter + 611642).Prime := by
  rw [fullRecordGapTerm10153_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10153, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10153_fast_pow_mod_ne_one

def fullRecordGapValue10154 : Nat := fullRecordGapCenterValue + 611868

theorem fullRecordGapTerm10154_eq_value :
    recordGapCenter + 611868 = fullRecordGapValue10154 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10154_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10154 (fullRecordGapValue10154 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10154_not_prime : ¬(recordGapCenter + 611868).Prime := by
  rw [fullRecordGapTerm10154_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10154, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10154_fast_pow_mod_ne_one

def fullRecordGapValue10155 : Nat := fullRecordGapCenterValue + 611922

theorem fullRecordGapTerm10155_eq_value :
    recordGapCenter + 611922 = fullRecordGapValue10155 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10155_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10155 (fullRecordGapValue10155 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10155_not_prime : ¬(recordGapCenter + 611922).Prime := by
  rw [fullRecordGapTerm10155_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10155, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10155_fast_pow_mod_ne_one

def fullRecordGapValue10156 : Nat := fullRecordGapCenterValue + 612012

theorem fullRecordGapTerm10156_eq_value :
    recordGapCenter + 612012 = fullRecordGapValue10156 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10156_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10156 (fullRecordGapValue10156 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10156_not_prime : ¬(recordGapCenter + 612012).Prime := by
  rw [fullRecordGapTerm10156_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10156, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10156_fast_pow_mod_ne_one

def fullRecordGapValue10157 : Nat := fullRecordGapCenterValue + 612038

theorem fullRecordGapTerm10157_eq_value :
    recordGapCenter + 612038 = fullRecordGapValue10157 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10157_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10157 (fullRecordGapValue10157 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10157_not_prime : ¬(recordGapCenter + 612038).Prime := by
  rw [fullRecordGapTerm10157_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10157, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10157_fast_pow_mod_ne_one

def fullRecordGapValue10158 : Nat := fullRecordGapCenterValue + 612152

theorem fullRecordGapTerm10158_eq_value :
    recordGapCenter + 612152 = fullRecordGapValue10158 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10158_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10158 (fullRecordGapValue10158 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10158_not_prime : ¬(recordGapCenter + 612152).Prime := by
  rw [fullRecordGapTerm10158_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10158, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10158_fast_pow_mod_ne_one

def fullRecordGapValue10159 : Nat := fullRecordGapCenterValue + 612182

theorem fullRecordGapTerm10159_eq_value :
    recordGapCenter + 612182 = fullRecordGapValue10159 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10159_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10159 (fullRecordGapValue10159 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10159_not_prime : ¬(recordGapCenter + 612182).Prime := by
  rw [fullRecordGapTerm10159_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10159, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10159_fast_pow_mod_ne_one

def fullRecordGapValue10160 : Nat := fullRecordGapCenterValue + 612230

theorem fullRecordGapTerm10160_eq_value :
    recordGapCenter + 612230 = fullRecordGapValue10160 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10160_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10160 (fullRecordGapValue10160 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10160_not_prime : ¬(recordGapCenter + 612230).Prime := by
  rw [fullRecordGapTerm10160_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10160, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10160_fast_pow_mod_ne_one

def fullRecordGapValue10161 : Nat := fullRecordGapCenterValue + 612308

theorem fullRecordGapTerm10161_eq_value :
    recordGapCenter + 612308 = fullRecordGapValue10161 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10161_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10161 (fullRecordGapValue10161 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10161_not_prime : ¬(recordGapCenter + 612308).Prime := by
  rw [fullRecordGapTerm10161_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10161, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10161_fast_pow_mod_ne_one

def fullRecordGapValue10162 : Nat := fullRecordGapCenterValue + 612452

theorem fullRecordGapTerm10162_eq_value :
    recordGapCenter + 612452 = fullRecordGapValue10162 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10162_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10162 (fullRecordGapValue10162 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10162_not_prime : ¬(recordGapCenter + 612452).Prime := by
  rw [fullRecordGapTerm10162_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10162, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10162_fast_pow_mod_ne_one

def fullRecordGapValue10163 : Nat := fullRecordGapCenterValue + 612488

theorem fullRecordGapTerm10163_eq_value :
    recordGapCenter + 612488 = fullRecordGapValue10163 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10163_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10163 (fullRecordGapValue10163 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10163_not_prime : ¬(recordGapCenter + 612488).Prime := by
  rw [fullRecordGapTerm10163_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10163, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10163_fast_pow_mod_ne_one

def fullRecordGapValue10164 : Nat := fullRecordGapCenterValue + 612516

theorem fullRecordGapTerm10164_eq_value :
    recordGapCenter + 612516 = fullRecordGapValue10164 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10164_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10164 (fullRecordGapValue10164 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10164_not_prime : ¬(recordGapCenter + 612516).Prime := by
  rw [fullRecordGapTerm10164_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10164, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10164_fast_pow_mod_ne_one

def fullRecordGapValue10165 : Nat := fullRecordGapCenterValue + 612626

theorem fullRecordGapTerm10165_eq_value :
    recordGapCenter + 612626 = fullRecordGapValue10165 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10165_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10165 (fullRecordGapValue10165 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10165_not_prime : ¬(recordGapCenter + 612626).Prime := by
  rw [fullRecordGapTerm10165_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10165, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10165_fast_pow_mod_ne_one

def fullRecordGapValue10166 : Nat := fullRecordGapCenterValue + 612698

theorem fullRecordGapTerm10166_eq_value :
    recordGapCenter + 612698 = fullRecordGapValue10166 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10166_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10166 (fullRecordGapValue10166 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10166_not_prime : ¬(recordGapCenter + 612698).Prime := by
  rw [fullRecordGapTerm10166_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10166, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10166_fast_pow_mod_ne_one

def fullRecordGapValue10167 : Nat := fullRecordGapCenterValue + 612732

theorem fullRecordGapTerm10167_eq_value :
    recordGapCenter + 612732 = fullRecordGapValue10167 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10167_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10167 (fullRecordGapValue10167 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10167_not_prime : ¬(recordGapCenter + 612732).Prime := by
  rw [fullRecordGapTerm10167_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10167, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10167_fast_pow_mod_ne_one

def fullRecordGapValue10168 : Nat := fullRecordGapCenterValue + 612776

theorem fullRecordGapTerm10168_eq_value :
    recordGapCenter + 612776 = fullRecordGapValue10168 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10168_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10168 (fullRecordGapValue10168 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10168_not_prime : ¬(recordGapCenter + 612776).Prime := by
  rw [fullRecordGapTerm10168_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10168, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10168_fast_pow_mod_ne_one

def fullRecordGapValue10169 : Nat := fullRecordGapCenterValue + 612962

theorem fullRecordGapTerm10169_eq_value :
    recordGapCenter + 612962 = fullRecordGapValue10169 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10169_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10169 (fullRecordGapValue10169 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10169_not_prime : ¬(recordGapCenter + 612962).Prime := by
  rw [fullRecordGapTerm10169_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10169, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10169_fast_pow_mod_ne_one

def fullRecordGapValue10170 : Nat := fullRecordGapCenterValue + 613022

theorem fullRecordGapTerm10170_eq_value :
    recordGapCenter + 613022 = fullRecordGapValue10170 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10170_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10170 (fullRecordGapValue10170 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10170_not_prime : ¬(recordGapCenter + 613022).Prime := by
  rw [fullRecordGapTerm10170_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10170, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10170_fast_pow_mod_ne_one

def fullRecordGapValue10171 : Nat := fullRecordGapCenterValue + 613046

theorem fullRecordGapTerm10171_eq_value :
    recordGapCenter + 613046 = fullRecordGapValue10171 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10171_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10171 (fullRecordGapValue10171 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10171_not_prime : ¬(recordGapCenter + 613046).Prime := by
  rw [fullRecordGapTerm10171_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10171, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10171_fast_pow_mod_ne_one

def fullRecordGapValue10172 : Nat := fullRecordGapCenterValue + 613058

theorem fullRecordGapTerm10172_eq_value :
    recordGapCenter + 613058 = fullRecordGapValue10172 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10172_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10172 (fullRecordGapValue10172 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10172_not_prime : ¬(recordGapCenter + 613058).Prime := by
  rw [fullRecordGapTerm10172_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10172, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10172_fast_pow_mod_ne_one

def fullRecordGapValue10173 : Nat := fullRecordGapCenterValue + 613082

theorem fullRecordGapTerm10173_eq_value :
    recordGapCenter + 613082 = fullRecordGapValue10173 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10173_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10173 (fullRecordGapValue10173 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10173_not_prime : ¬(recordGapCenter + 613082).Prime := by
  rw [fullRecordGapTerm10173_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10173, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10173_fast_pow_mod_ne_one

def fullRecordGapValue10174 : Nat := fullRecordGapCenterValue + 613086

theorem fullRecordGapTerm10174_eq_value :
    recordGapCenter + 613086 = fullRecordGapValue10174 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10174_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10174 (fullRecordGapValue10174 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10174_not_prime : ¬(recordGapCenter + 613086).Prime := by
  rw [fullRecordGapTerm10174_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10174, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10174_fast_pow_mod_ne_one

def fullRecordGapValue10175 : Nat := fullRecordGapCenterValue + 613148

theorem fullRecordGapTerm10175_eq_value :
    recordGapCenter + 613148 = fullRecordGapValue10175 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10175_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10175 (fullRecordGapValue10175 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10175_not_prime : ¬(recordGapCenter + 613148).Prime := by
  rw [fullRecordGapTerm10175_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10175, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10175_fast_pow_mod_ne_one

def fullRecordGapValue10176 : Nat := fullRecordGapCenterValue + 613182

theorem fullRecordGapTerm10176_eq_value :
    recordGapCenter + 613182 = fullRecordGapValue10176 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10176_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10176 (fullRecordGapValue10176 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10176_not_prime : ¬(recordGapCenter + 613182).Prime := by
  rw [fullRecordGapTerm10176_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10176, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10176_fast_pow_mod_ne_one

def fullRecordGapValue10177 : Nat := fullRecordGapCenterValue + 613208

theorem fullRecordGapTerm10177_eq_value :
    recordGapCenter + 613208 = fullRecordGapValue10177 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10177_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10177 (fullRecordGapValue10177 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10177_not_prime : ¬(recordGapCenter + 613208).Prime := by
  rw [fullRecordGapTerm10177_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10177, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10177_fast_pow_mod_ne_one

def fullRecordGapValue10178 : Nat := fullRecordGapCenterValue + 613308

theorem fullRecordGapTerm10178_eq_value :
    recordGapCenter + 613308 = fullRecordGapValue10178 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10178_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10178 (fullRecordGapValue10178 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10178_not_prime : ¬(recordGapCenter + 613308).Prime := by
  rw [fullRecordGapTerm10178_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10178, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10178_fast_pow_mod_ne_one

def fullRecordGapValue10179 : Nat := fullRecordGapCenterValue + 613406

theorem fullRecordGapTerm10179_eq_value :
    recordGapCenter + 613406 = fullRecordGapValue10179 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10179_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10179 (fullRecordGapValue10179 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10179_not_prime : ¬(recordGapCenter + 613406).Prime := by
  rw [fullRecordGapTerm10179_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10179, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10179_fast_pow_mod_ne_one

def fullRecordGapValue10180 : Nat := fullRecordGapCenterValue + 613506

theorem fullRecordGapTerm10180_eq_value :
    recordGapCenter + 613506 = fullRecordGapValue10180 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10180_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10180 (fullRecordGapValue10180 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10180_not_prime : ¬(recordGapCenter + 613506).Prime := by
  rw [fullRecordGapTerm10180_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10180, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10180_fast_pow_mod_ne_one

def fullRecordGapValue10181 : Nat := fullRecordGapCenterValue + 613518

theorem fullRecordGapTerm10181_eq_value :
    recordGapCenter + 613518 = fullRecordGapValue10181 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10181_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10181 (fullRecordGapValue10181 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10181_not_prime : ¬(recordGapCenter + 613518).Prime := by
  rw [fullRecordGapTerm10181_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10181, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10181_fast_pow_mod_ne_one

def fullRecordGapValue10182 : Nat := fullRecordGapCenterValue + 613562

theorem fullRecordGapTerm10182_eq_value :
    recordGapCenter + 613562 = fullRecordGapValue10182 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10182_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10182 (fullRecordGapValue10182 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10182_not_prime : ¬(recordGapCenter + 613562).Prime := by
  rw [fullRecordGapTerm10182_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10182, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10182_fast_pow_mod_ne_one

def fullRecordGapValue10183 : Nat := fullRecordGapCenterValue + 613572

theorem fullRecordGapTerm10183_eq_value :
    recordGapCenter + 613572 = fullRecordGapValue10183 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10183_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10183 (fullRecordGapValue10183 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10183_not_prime : ¬(recordGapCenter + 613572).Prime := by
  rw [fullRecordGapTerm10183_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10183, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10183_fast_pow_mod_ne_one

def fullRecordGapValue10184 : Nat := fullRecordGapCenterValue + 613596

theorem fullRecordGapTerm10184_eq_value :
    recordGapCenter + 613596 = fullRecordGapValue10184 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10184_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10184 (fullRecordGapValue10184 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10184_not_prime : ¬(recordGapCenter + 613596).Prime := by
  rw [fullRecordGapTerm10184_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10184, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10184_fast_pow_mod_ne_one

def fullRecordGapValue10185 : Nat := fullRecordGapCenterValue + 613628

theorem fullRecordGapTerm10185_eq_value :
    recordGapCenter + 613628 = fullRecordGapValue10185 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10185_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10185 (fullRecordGapValue10185 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10185_not_prime : ¬(recordGapCenter + 613628).Prime := by
  rw [fullRecordGapTerm10185_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10185, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10185_fast_pow_mod_ne_one

def fullRecordGapValue10186 : Nat := fullRecordGapCenterValue + 613758

theorem fullRecordGapTerm10186_eq_value :
    recordGapCenter + 613758 = fullRecordGapValue10186 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10186_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10186 (fullRecordGapValue10186 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10186_not_prime : ¬(recordGapCenter + 613758).Prime := by
  rw [fullRecordGapTerm10186_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10186, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10186_fast_pow_mod_ne_one

def fullRecordGapValue10187 : Nat := fullRecordGapCenterValue + 613790

theorem fullRecordGapTerm10187_eq_value :
    recordGapCenter + 613790 = fullRecordGapValue10187 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10187_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10187 (fullRecordGapValue10187 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10187_not_prime : ¬(recordGapCenter + 613790).Prime := by
  rw [fullRecordGapTerm10187_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10187, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10187_fast_pow_mod_ne_one

def fullRecordGapValue10188 : Nat := fullRecordGapCenterValue + 613806

theorem fullRecordGapTerm10188_eq_value :
    recordGapCenter + 613806 = fullRecordGapValue10188 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10188_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10188 (fullRecordGapValue10188 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10188_not_prime : ¬(recordGapCenter + 613806).Prime := by
  rw [fullRecordGapTerm10188_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10188, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10188_fast_pow_mod_ne_one

def fullRecordGapValue10189 : Nat := fullRecordGapCenterValue + 613902

theorem fullRecordGapTerm10189_eq_value :
    recordGapCenter + 613902 = fullRecordGapValue10189 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10189_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10189 (fullRecordGapValue10189 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10189_not_prime : ¬(recordGapCenter + 613902).Prime := by
  rw [fullRecordGapTerm10189_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10189, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10189_fast_pow_mod_ne_one

def fullRecordGapValue10190 : Nat := fullRecordGapCenterValue + 614030

theorem fullRecordGapTerm10190_eq_value :
    recordGapCenter + 614030 = fullRecordGapValue10190 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10190_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10190 (fullRecordGapValue10190 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10190_not_prime : ¬(recordGapCenter + 614030).Prime := by
  rw [fullRecordGapTerm10190_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10190, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10190_fast_pow_mod_ne_one

def fullRecordGapValue10191 : Nat := fullRecordGapCenterValue + 614132

theorem fullRecordGapTerm10191_eq_value :
    recordGapCenter + 614132 = fullRecordGapValue10191 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10191_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10191 (fullRecordGapValue10191 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10191_not_prime : ¬(recordGapCenter + 614132).Prime := by
  rw [fullRecordGapTerm10191_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10191, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10191_fast_pow_mod_ne_one

def fullRecordGapValue10192 : Nat := fullRecordGapCenterValue + 614168

theorem fullRecordGapTerm10192_eq_value :
    recordGapCenter + 614168 = fullRecordGapValue10192 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10192_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10192 (fullRecordGapValue10192 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10192_not_prime : ¬(recordGapCenter + 614168).Prime := by
  rw [fullRecordGapTerm10192_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10192, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10192_fast_pow_mod_ne_one

def fullRecordGapValue10193 : Nat := fullRecordGapCenterValue + 614342

theorem fullRecordGapTerm10193_eq_value :
    recordGapCenter + 614342 = fullRecordGapValue10193 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10193_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10193 (fullRecordGapValue10193 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10193_not_prime : ¬(recordGapCenter + 614342).Prime := by
  rw [fullRecordGapTerm10193_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10193, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10193_fast_pow_mod_ne_one

def fullRecordGapValue10194 : Nat := fullRecordGapCenterValue + 614378

theorem fullRecordGapTerm10194_eq_value :
    recordGapCenter + 614378 = fullRecordGapValue10194 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10194_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10194 (fullRecordGapValue10194 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10194_not_prime : ¬(recordGapCenter + 614378).Prime := by
  rw [fullRecordGapTerm10194_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10194, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10194_fast_pow_mod_ne_one

def fullRecordGapValue10195 : Nat := fullRecordGapCenterValue + 614408

theorem fullRecordGapTerm10195_eq_value :
    recordGapCenter + 614408 = fullRecordGapValue10195 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10195_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10195 (fullRecordGapValue10195 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10195_not_prime : ¬(recordGapCenter + 614408).Prime := by
  rw [fullRecordGapTerm10195_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10195, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10195_fast_pow_mod_ne_one

def fullRecordGapValue10196 : Nat := fullRecordGapCenterValue + 614436

theorem fullRecordGapTerm10196_eq_value :
    recordGapCenter + 614436 = fullRecordGapValue10196 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10196_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10196 (fullRecordGapValue10196 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10196_not_prime : ¬(recordGapCenter + 614436).Prime := by
  rw [fullRecordGapTerm10196_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10196, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10196_fast_pow_mod_ne_one

def fullRecordGapValue10197 : Nat := fullRecordGapCenterValue + 614486

theorem fullRecordGapTerm10197_eq_value :
    recordGapCenter + 614486 = fullRecordGapValue10197 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10197_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10197 (fullRecordGapValue10197 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10197_not_prime : ¬(recordGapCenter + 614486).Prime := by
  rw [fullRecordGapTerm10197_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10197, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10197_fast_pow_mod_ne_one

def fullRecordGapValue10198 : Nat := fullRecordGapCenterValue + 614546

theorem fullRecordGapTerm10198_eq_value :
    recordGapCenter + 614546 = fullRecordGapValue10198 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10198_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10198 (fullRecordGapValue10198 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10198_not_prime : ¬(recordGapCenter + 614546).Prime := by
  rw [fullRecordGapTerm10198_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10198, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10198_fast_pow_mod_ne_one

def fullRecordGapValue10199 : Nat := fullRecordGapCenterValue + 614552

theorem fullRecordGapTerm10199_eq_value :
    recordGapCenter + 614552 = fullRecordGapValue10199 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10199_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10199 (fullRecordGapValue10199 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10199_not_prime : ¬(recordGapCenter + 614552).Prime := by
  rw [fullRecordGapTerm10199_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10199, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10199_fast_pow_mod_ne_one

def fullRecordGapValue10200 : Nat := fullRecordGapCenterValue + 614598

theorem fullRecordGapTerm10200_eq_value :
    recordGapCenter + 614598 = fullRecordGapValue10200 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10200_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10200 (fullRecordGapValue10200 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10200_not_prime : ¬(recordGapCenter + 614598).Prime := by
  rw [fullRecordGapTerm10200_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10200, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10200_fast_pow_mod_ne_one

def fullRecordGapValue10201 : Nat := fullRecordGapCenterValue + 614630

theorem fullRecordGapTerm10201_eq_value :
    recordGapCenter + 614630 = fullRecordGapValue10201 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10201_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10201 (fullRecordGapValue10201 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10201_not_prime : ¬(recordGapCenter + 614630).Prime := by
  rw [fullRecordGapTerm10201_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10201, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10201_fast_pow_mod_ne_one

def fullRecordGapValue10202 : Nat := fullRecordGapCenterValue + 614678

theorem fullRecordGapTerm10202_eq_value :
    recordGapCenter + 614678 = fullRecordGapValue10202 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10202_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10202 (fullRecordGapValue10202 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10202_not_prime : ¬(recordGapCenter + 614678).Prime := by
  rw [fullRecordGapTerm10202_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10202, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10202_fast_pow_mod_ne_one

def fullRecordGapValue10203 : Nat := fullRecordGapCenterValue + 614696

theorem fullRecordGapTerm10203_eq_value :
    recordGapCenter + 614696 = fullRecordGapValue10203 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10203_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10203 (fullRecordGapValue10203 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10203_not_prime : ¬(recordGapCenter + 614696).Prime := by
  rw [fullRecordGapTerm10203_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10203, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10203_fast_pow_mod_ne_one

def fullRecordGapValue10204 : Nat := fullRecordGapCenterValue + 614706

theorem fullRecordGapTerm10204_eq_value :
    recordGapCenter + 614706 = fullRecordGapValue10204 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10204_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10204 (fullRecordGapValue10204 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10204_not_prime : ¬(recordGapCenter + 614706).Prime := by
  rw [fullRecordGapTerm10204_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10204, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10204_fast_pow_mod_ne_one

def fullRecordGapValue10205 : Nat := fullRecordGapCenterValue + 614748

theorem fullRecordGapTerm10205_eq_value :
    recordGapCenter + 614748 = fullRecordGapValue10205 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10205_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10205 (fullRecordGapValue10205 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10205_not_prime : ¬(recordGapCenter + 614748).Prime := by
  rw [fullRecordGapTerm10205_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10205, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10205_fast_pow_mod_ne_one

def fullRecordGapValue10206 : Nat := fullRecordGapCenterValue + 614756

theorem fullRecordGapTerm10206_eq_value :
    recordGapCenter + 614756 = fullRecordGapValue10206 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10206_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10206 (fullRecordGapValue10206 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10206_not_prime : ¬(recordGapCenter + 614756).Prime := by
  rw [fullRecordGapTerm10206_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10206, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10206_fast_pow_mod_ne_one

def fullRecordGapValue10207 : Nat := fullRecordGapCenterValue + 614868

theorem fullRecordGapTerm10207_eq_value :
    recordGapCenter + 614868 = fullRecordGapValue10207 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10207_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10207 (fullRecordGapValue10207 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10207_not_prime : ¬(recordGapCenter + 614868).Prime := by
  rw [fullRecordGapTerm10207_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10207, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10207_fast_pow_mod_ne_one

def fullRecordGapValue10208 : Nat := fullRecordGapCenterValue + 614892

theorem fullRecordGapTerm10208_eq_value :
    recordGapCenter + 614892 = fullRecordGapValue10208 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10208_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10208 (fullRecordGapValue10208 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10208_not_prime : ¬(recordGapCenter + 614892).Prime := by
  rw [fullRecordGapTerm10208_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10208, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10208_fast_pow_mod_ne_one

def fullRecordGapValue10209 : Nat := fullRecordGapCenterValue + 614922

theorem fullRecordGapTerm10209_eq_value :
    recordGapCenter + 614922 = fullRecordGapValue10209 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10209_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10209 (fullRecordGapValue10209 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10209_not_prime : ¬(recordGapCenter + 614922).Prime := by
  rw [fullRecordGapTerm10209_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10209, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10209_fast_pow_mod_ne_one

def fullRecordGapValue10210 : Nat := fullRecordGapCenterValue + 614930

theorem fullRecordGapTerm10210_eq_value :
    recordGapCenter + 614930 = fullRecordGapValue10210 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10210_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10210 (fullRecordGapValue10210 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10210_not_prime : ¬(recordGapCenter + 614930).Prime := by
  rw [fullRecordGapTerm10210_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10210, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10210_fast_pow_mod_ne_one

def fullRecordGapValue10211 : Nat := fullRecordGapCenterValue + 614982

theorem fullRecordGapTerm10211_eq_value :
    recordGapCenter + 614982 = fullRecordGapValue10211 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10211_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10211 (fullRecordGapValue10211 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10211_not_prime : ¬(recordGapCenter + 614982).Prime := by
  rw [fullRecordGapTerm10211_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10211, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10211_fast_pow_mod_ne_one

def fullRecordGapValue10212 : Nat := fullRecordGapCenterValue + 615198

theorem fullRecordGapTerm10212_eq_value :
    recordGapCenter + 615198 = fullRecordGapValue10212 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10212_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10212 (fullRecordGapValue10212 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10212_not_prime : ¬(recordGapCenter + 615198).Prime := by
  rw [fullRecordGapTerm10212_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10212, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10212_fast_pow_mod_ne_one

def fullRecordGapValue10213 : Nat := fullRecordGapCenterValue + 615282

theorem fullRecordGapTerm10213_eq_value :
    recordGapCenter + 615282 = fullRecordGapValue10213 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10213_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10213 (fullRecordGapValue10213 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10213_not_prime : ¬(recordGapCenter + 615282).Prime := by
  rw [fullRecordGapTerm10213_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10213, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10213_fast_pow_mod_ne_one

def fullRecordGapValue10214 : Nat := fullRecordGapCenterValue + 615386

theorem fullRecordGapTerm10214_eq_value :
    recordGapCenter + 615386 = fullRecordGapValue10214 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10214_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10214 (fullRecordGapValue10214 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10214_not_prime : ¬(recordGapCenter + 615386).Prime := by
  rw [fullRecordGapTerm10214_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10214, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10214_fast_pow_mod_ne_one

def fullRecordGapValue10215 : Nat := fullRecordGapCenterValue + 615566

theorem fullRecordGapTerm10215_eq_value :
    recordGapCenter + 615566 = fullRecordGapValue10215 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10215_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10215 (fullRecordGapValue10215 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10215_not_prime : ¬(recordGapCenter + 615566).Prime := by
  rw [fullRecordGapTerm10215_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10215, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10215_fast_pow_mod_ne_one

def fullRecordGapValue10216 : Nat := fullRecordGapCenterValue + 615590

theorem fullRecordGapTerm10216_eq_value :
    recordGapCenter + 615590 = fullRecordGapValue10216 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10216_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10216 (fullRecordGapValue10216 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10216_not_prime : ¬(recordGapCenter + 615590).Prime := by
  rw [fullRecordGapTerm10216_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10216, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10216_fast_pow_mod_ne_one

def fullRecordGapValue10217 : Nat := fullRecordGapCenterValue + 615746

theorem fullRecordGapTerm10217_eq_value :
    recordGapCenter + 615746 = fullRecordGapValue10217 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10217_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10217 (fullRecordGapValue10217 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10217_not_prime : ¬(recordGapCenter + 615746).Prime := by
  rw [fullRecordGapTerm10217_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10217, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10217_fast_pow_mod_ne_one

def fullRecordGapValue10218 : Nat := fullRecordGapCenterValue + 615788

theorem fullRecordGapTerm10218_eq_value :
    recordGapCenter + 615788 = fullRecordGapValue10218 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10218_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10218 (fullRecordGapValue10218 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10218_not_prime : ¬(recordGapCenter + 615788).Prime := by
  rw [fullRecordGapTerm10218_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10218, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10218_fast_pow_mod_ne_one

def fullRecordGapValue10219 : Nat := fullRecordGapCenterValue + 615830

theorem fullRecordGapTerm10219_eq_value :
    recordGapCenter + 615830 = fullRecordGapValue10219 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10219_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10219 (fullRecordGapValue10219 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10219_not_prime : ¬(recordGapCenter + 615830).Prime := by
  rw [fullRecordGapTerm10219_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10219, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10219_fast_pow_mod_ne_one

def fullRecordGapValue10220 : Nat := fullRecordGapCenterValue + 615878

theorem fullRecordGapTerm10220_eq_value :
    recordGapCenter + 615878 = fullRecordGapValue10220 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10220_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10220 (fullRecordGapValue10220 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10220_not_prime : ¬(recordGapCenter + 615878).Prime := by
  rw [fullRecordGapTerm10220_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10220, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10220_fast_pow_mod_ne_one

def fullRecordGapValue10221 : Nat := fullRecordGapCenterValue + 615918

theorem fullRecordGapTerm10221_eq_value :
    recordGapCenter + 615918 = fullRecordGapValue10221 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10221_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10221 (fullRecordGapValue10221 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10221_not_prime : ¬(recordGapCenter + 615918).Prime := by
  rw [fullRecordGapTerm10221_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10221, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10221_fast_pow_mod_ne_one

def fullRecordGapValue10222 : Nat := fullRecordGapCenterValue + 615938

theorem fullRecordGapTerm10222_eq_value :
    recordGapCenter + 615938 = fullRecordGapValue10222 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10222_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10222 (fullRecordGapValue10222 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10222_not_prime : ¬(recordGapCenter + 615938).Prime := by
  rw [fullRecordGapTerm10222_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10222, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10222_fast_pow_mod_ne_one

def fullRecordGapValue10223 : Nat := fullRecordGapCenterValue + 616038

theorem fullRecordGapTerm10223_eq_value :
    recordGapCenter + 616038 = fullRecordGapValue10223 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10223_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10223 (fullRecordGapValue10223 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10223_not_prime : ¬(recordGapCenter + 616038).Prime := by
  rw [fullRecordGapTerm10223_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10223, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10223_fast_pow_mod_ne_one

def fullRecordGapValue10224 : Nat := fullRecordGapCenterValue + 616082

theorem fullRecordGapTerm10224_eq_value :
    recordGapCenter + 616082 = fullRecordGapValue10224 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10224_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10224 (fullRecordGapValue10224 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10224_not_prime : ¬(recordGapCenter + 616082).Prime := by
  rw [fullRecordGapTerm10224_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10224, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10224_fast_pow_mod_ne_one

def fullRecordGapValue10225 : Nat := fullRecordGapCenterValue + 616092

theorem fullRecordGapTerm10225_eq_value :
    recordGapCenter + 616092 = fullRecordGapValue10225 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10225_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10225 (fullRecordGapValue10225 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10225_not_prime : ¬(recordGapCenter + 616092).Prime := by
  rw [fullRecordGapTerm10225_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10225, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10225_fast_pow_mod_ne_one

def fullRecordGapValue10226 : Nat := fullRecordGapCenterValue + 616136

theorem fullRecordGapTerm10226_eq_value :
    recordGapCenter + 616136 = fullRecordGapValue10226 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10226_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10226 (fullRecordGapValue10226 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10226_not_prime : ¬(recordGapCenter + 616136).Prime := by
  rw [fullRecordGapTerm10226_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10226, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10226_fast_pow_mod_ne_one

def fullRecordGapValue10227 : Nat := fullRecordGapCenterValue + 616292

theorem fullRecordGapTerm10227_eq_value :
    recordGapCenter + 616292 = fullRecordGapValue10227 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10227_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10227 (fullRecordGapValue10227 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10227_not_prime : ¬(recordGapCenter + 616292).Prime := by
  rw [fullRecordGapTerm10227_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10227, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10227_fast_pow_mod_ne_one

def fullRecordGapValue10228 : Nat := fullRecordGapCenterValue + 616298

theorem fullRecordGapTerm10228_eq_value :
    recordGapCenter + 616298 = fullRecordGapValue10228 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10228_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10228 (fullRecordGapValue10228 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10228_not_prime : ¬(recordGapCenter + 616298).Prime := by
  rw [fullRecordGapTerm10228_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10228, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10228_fast_pow_mod_ne_one

def fullRecordGapValue10229 : Nat := fullRecordGapCenterValue + 616316

theorem fullRecordGapTerm10229_eq_value :
    recordGapCenter + 616316 = fullRecordGapValue10229 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10229_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10229 (fullRecordGapValue10229 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10229_not_prime : ¬(recordGapCenter + 616316).Prime := by
  rw [fullRecordGapTerm10229_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10229, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10229_fast_pow_mod_ne_one

def fullRecordGapValue10230 : Nat := fullRecordGapCenterValue + 616406

theorem fullRecordGapTerm10230_eq_value :
    recordGapCenter + 616406 = fullRecordGapValue10230 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10230_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10230 (fullRecordGapValue10230 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10230_not_prime : ¬(recordGapCenter + 616406).Prime := by
  rw [fullRecordGapTerm10230_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10230, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10230_fast_pow_mod_ne_one

def fullRecordGapValue10231 : Nat := fullRecordGapCenterValue + 616526

theorem fullRecordGapTerm10231_eq_value :
    recordGapCenter + 616526 = fullRecordGapValue10231 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10231_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10231 (fullRecordGapValue10231 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10231_not_prime : ¬(recordGapCenter + 616526).Prime := by
  rw [fullRecordGapTerm10231_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10231, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10231_fast_pow_mod_ne_one

def fullRecordGapValue10232 : Nat := fullRecordGapCenterValue + 616578

theorem fullRecordGapTerm10232_eq_value :
    recordGapCenter + 616578 = fullRecordGapValue10232 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10232_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10232 (fullRecordGapValue10232 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10232_not_prime : ¬(recordGapCenter + 616578).Prime := by
  rw [fullRecordGapTerm10232_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10232, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10232_fast_pow_mod_ne_one

def fullRecordGapValue10233 : Nat := fullRecordGapCenterValue + 616596

theorem fullRecordGapTerm10233_eq_value :
    recordGapCenter + 616596 = fullRecordGapValue10233 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10233_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10233 (fullRecordGapValue10233 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10233_not_prime : ¬(recordGapCenter + 616596).Prime := by
  rw [fullRecordGapTerm10233_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10233, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10233_fast_pow_mod_ne_one

def fullRecordGapValue10234 : Nat := fullRecordGapCenterValue + 616628

theorem fullRecordGapTerm10234_eq_value :
    recordGapCenter + 616628 = fullRecordGapValue10234 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10234_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10234 (fullRecordGapValue10234 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10234_not_prime : ¬(recordGapCenter + 616628).Prime := by
  rw [fullRecordGapTerm10234_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10234, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10234_fast_pow_mod_ne_one

def fullRecordGapValue10235 : Nat := fullRecordGapCenterValue + 616718

theorem fullRecordGapTerm10235_eq_value :
    recordGapCenter + 616718 = fullRecordGapValue10235 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10235_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10235 (fullRecordGapValue10235 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10235_not_prime : ¬(recordGapCenter + 616718).Prime := by
  rw [fullRecordGapTerm10235_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10235, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10235_fast_pow_mod_ne_one

def fullRecordGapValue10236 : Nat := fullRecordGapCenterValue + 616782

theorem fullRecordGapTerm10236_eq_value :
    recordGapCenter + 616782 = fullRecordGapValue10236 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10236_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10236 (fullRecordGapValue10236 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10236_not_prime : ¬(recordGapCenter + 616782).Prime := by
  rw [fullRecordGapTerm10236_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10236, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10236_fast_pow_mod_ne_one

def fullRecordGapValue10237 : Nat := fullRecordGapCenterValue + 616866

theorem fullRecordGapTerm10237_eq_value :
    recordGapCenter + 616866 = fullRecordGapValue10237 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10237_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10237 (fullRecordGapValue10237 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10237_not_prime : ¬(recordGapCenter + 616866).Prime := by
  rw [fullRecordGapTerm10237_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10237, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10237_fast_pow_mod_ne_one

def fullRecordGapValue10238 : Nat := fullRecordGapCenterValue + 617018

theorem fullRecordGapTerm10238_eq_value :
    recordGapCenter + 617018 = fullRecordGapValue10238 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10238_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10238 (fullRecordGapValue10238 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10238_not_prime : ¬(recordGapCenter + 617018).Prime := by
  rw [fullRecordGapTerm10238_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10238, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10238_fast_pow_mod_ne_one

def fullRecordGapValue10239 : Nat := fullRecordGapCenterValue + 617046

theorem fullRecordGapTerm10239_eq_value :
    recordGapCenter + 617046 = fullRecordGapValue10239 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10239_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10239 (fullRecordGapValue10239 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10239_not_prime : ¬(recordGapCenter + 617046).Prime := by
  rw [fullRecordGapTerm10239_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10239, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10239_fast_pow_mod_ne_one

def fullRecordGapValue10240 : Nat := fullRecordGapCenterValue + 617102

theorem fullRecordGapTerm10240_eq_value :
    recordGapCenter + 617102 = fullRecordGapValue10240 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral10240_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue10240 (fullRecordGapValue10240 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10240_not_prime : ¬(recordGapCenter + 617102).Prime := by
  rw [fullRecordGapTerm10240_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue10240, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral10240_fast_pow_mod_ne_one

end PrimeFactorUnimodality
