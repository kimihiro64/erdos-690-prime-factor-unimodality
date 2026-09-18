import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue00001 : Nat := fullRecordGapCenterValue - 455622

theorem fullRecordGapTerm00001_eq_value :
    recordGapCenter - 455622 = fullRecordGapValue00001 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00001_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00001 (fullRecordGapValue00001 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00001_not_prime : ¬(recordGapCenter - 455622).Prime := by
  rw [fullRecordGapTerm00001_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00001, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00001_fast_pow_mod_ne_one

def fullRecordGapValue00002 : Nat := fullRecordGapCenterValue - 455458

theorem fullRecordGapTerm00002_eq_value :
    recordGapCenter - 455458 = fullRecordGapValue00002 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00002_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00002 (fullRecordGapValue00002 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00002_not_prime : ¬(recordGapCenter - 455458).Prime := by
  rw [fullRecordGapTerm00002_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00002, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00002_fast_pow_mod_ne_one

def fullRecordGapValue00003 : Nat := fullRecordGapCenterValue - 455410

theorem fullRecordGapTerm00003_eq_value :
    recordGapCenter - 455410 = fullRecordGapValue00003 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00003_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00003 (fullRecordGapValue00003 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00003_not_prime : ¬(recordGapCenter - 455410).Prime := by
  rw [fullRecordGapTerm00003_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00003, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00003_fast_pow_mod_ne_one

def fullRecordGapValue00004 : Nat := fullRecordGapCenterValue - 455368

theorem fullRecordGapTerm00004_eq_value :
    recordGapCenter - 455368 = fullRecordGapValue00004 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00004_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00004 (fullRecordGapValue00004 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00004_not_prime : ¬(recordGapCenter - 455368).Prime := by
  rw [fullRecordGapTerm00004_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00004, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00004_fast_pow_mod_ne_one

def fullRecordGapValue00005 : Nat := fullRecordGapCenterValue - 455298

theorem fullRecordGapTerm00005_eq_value :
    recordGapCenter - 455298 = fullRecordGapValue00005 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00005_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00005 (fullRecordGapValue00005 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00005_not_prime : ¬(recordGapCenter - 455298).Prime := by
  rw [fullRecordGapTerm00005_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00005, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00005_fast_pow_mod_ne_one

def fullRecordGapValue00006 : Nat := fullRecordGapCenterValue - 455254

theorem fullRecordGapTerm00006_eq_value :
    recordGapCenter - 455254 = fullRecordGapValue00006 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00006_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00006 (fullRecordGapValue00006 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00006_not_prime : ¬(recordGapCenter - 455254).Prime := by
  rw [fullRecordGapTerm00006_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00006, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00006_fast_pow_mod_ne_one

def fullRecordGapValue00007 : Nat := fullRecordGapCenterValue - 455214

theorem fullRecordGapTerm00007_eq_value :
    recordGapCenter - 455214 = fullRecordGapValue00007 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00007_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00007 (fullRecordGapValue00007 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00007_not_prime : ¬(recordGapCenter - 455214).Prime := by
  rw [fullRecordGapTerm00007_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00007, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00007_fast_pow_mod_ne_one

def fullRecordGapValue00008 : Nat := fullRecordGapCenterValue - 455194

theorem fullRecordGapTerm00008_eq_value :
    recordGapCenter - 455194 = fullRecordGapValue00008 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00008_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00008 (fullRecordGapValue00008 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00008_not_prime : ¬(recordGapCenter - 455194).Prime := by
  rw [fullRecordGapTerm00008_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00008, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00008_fast_pow_mod_ne_one

def fullRecordGapValue00009 : Nat := fullRecordGapCenterValue - 454984

theorem fullRecordGapTerm00009_eq_value :
    recordGapCenter - 454984 = fullRecordGapValue00009 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00009_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00009 (fullRecordGapValue00009 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00009_not_prime : ¬(recordGapCenter - 454984).Prime := by
  rw [fullRecordGapTerm00009_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00009, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00009_fast_pow_mod_ne_one

def fullRecordGapValue00010 : Nat := fullRecordGapCenterValue - 454978

theorem fullRecordGapTerm00010_eq_value :
    recordGapCenter - 454978 = fullRecordGapValue00010 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00010_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00010 (fullRecordGapValue00010 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00010_not_prime : ¬(recordGapCenter - 454978).Prime := by
  rw [fullRecordGapTerm00010_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00010, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00010_fast_pow_mod_ne_one

def fullRecordGapValue00011 : Nat := fullRecordGapCenterValue - 454782

theorem fullRecordGapTerm00011_eq_value :
    recordGapCenter - 454782 = fullRecordGapValue00011 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00011_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00011 (fullRecordGapValue00011 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00011_not_prime : ¬(recordGapCenter - 454782).Prime := by
  rw [fullRecordGapTerm00011_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00011, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00011_fast_pow_mod_ne_one

def fullRecordGapValue00012 : Nat := fullRecordGapCenterValue - 454758

theorem fullRecordGapTerm00012_eq_value :
    recordGapCenter - 454758 = fullRecordGapValue00012 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00012_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00012 (fullRecordGapValue00012 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00012_not_prime : ¬(recordGapCenter - 454758).Prime := by
  rw [fullRecordGapTerm00012_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00012, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00012_fast_pow_mod_ne_one

def fullRecordGapValue00013 : Nat := fullRecordGapCenterValue - 454732

theorem fullRecordGapTerm00013_eq_value :
    recordGapCenter - 454732 = fullRecordGapValue00013 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00013_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00013 (fullRecordGapValue00013 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00013_not_prime : ¬(recordGapCenter - 454732).Prime := by
  rw [fullRecordGapTerm00013_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00013, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00013_fast_pow_mod_ne_one

def fullRecordGapValue00014 : Nat := fullRecordGapCenterValue - 454492

theorem fullRecordGapTerm00014_eq_value :
    recordGapCenter - 454492 = fullRecordGapValue00014 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00014_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00014 (fullRecordGapValue00014 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00014_not_prime : ¬(recordGapCenter - 454492).Prime := by
  rw [fullRecordGapTerm00014_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00014, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00014_fast_pow_mod_ne_one

def fullRecordGapValue00015 : Nat := fullRecordGapCenterValue - 454330

theorem fullRecordGapTerm00015_eq_value :
    recordGapCenter - 454330 = fullRecordGapValue00015 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00015_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00015 (fullRecordGapValue00015 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00015_not_prime : ¬(recordGapCenter - 454330).Prime := by
  rw [fullRecordGapTerm00015_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00015, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00015_fast_pow_mod_ne_one

def fullRecordGapValue00016 : Nat := fullRecordGapCenterValue - 454270

theorem fullRecordGapTerm00016_eq_value :
    recordGapCenter - 454270 = fullRecordGapValue00016 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00016_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00016 (fullRecordGapValue00016 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00016_not_prime : ¬(recordGapCenter - 454270).Prime := by
  rw [fullRecordGapTerm00016_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00016, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00016_fast_pow_mod_ne_one

def fullRecordGapValue00017 : Nat := fullRecordGapCenterValue - 454264

theorem fullRecordGapTerm00017_eq_value :
    recordGapCenter - 454264 = fullRecordGapValue00017 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00017_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00017 (fullRecordGapValue00017 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00017_not_prime : ¬(recordGapCenter - 454264).Prime := by
  rw [fullRecordGapTerm00017_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00017, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00017_fast_pow_mod_ne_one

def fullRecordGapValue00018 : Nat := fullRecordGapCenterValue - 454242

theorem fullRecordGapTerm00018_eq_value :
    recordGapCenter - 454242 = fullRecordGapValue00018 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00018_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00018 (fullRecordGapValue00018 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00018_not_prime : ¬(recordGapCenter - 454242).Prime := by
  rw [fullRecordGapTerm00018_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00018, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00018_fast_pow_mod_ne_one

def fullRecordGapValue00019 : Nat := fullRecordGapCenterValue - 454228

theorem fullRecordGapTerm00019_eq_value :
    recordGapCenter - 454228 = fullRecordGapValue00019 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00019_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00019 (fullRecordGapValue00019 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00019_not_prime : ¬(recordGapCenter - 454228).Prime := by
  rw [fullRecordGapTerm00019_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00019, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00019_fast_pow_mod_ne_one

def fullRecordGapValue00020 : Nat := fullRecordGapCenterValue - 454218

theorem fullRecordGapTerm00020_eq_value :
    recordGapCenter - 454218 = fullRecordGapValue00020 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00020_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00020 (fullRecordGapValue00020 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00020_not_prime : ¬(recordGapCenter - 454218).Prime := by
  rw [fullRecordGapTerm00020_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00020, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00020_fast_pow_mod_ne_one

def fullRecordGapValue00021 : Nat := fullRecordGapCenterValue - 454074

theorem fullRecordGapTerm00021_eq_value :
    recordGapCenter - 454074 = fullRecordGapValue00021 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00021_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00021 (fullRecordGapValue00021 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00021_not_prime : ¬(recordGapCenter - 454074).Prime := by
  rw [fullRecordGapTerm00021_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00021, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00021_fast_pow_mod_ne_one

def fullRecordGapValue00022 : Nat := fullRecordGapCenterValue - 454054

theorem fullRecordGapTerm00022_eq_value :
    recordGapCenter - 454054 = fullRecordGapValue00022 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00022_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00022 (fullRecordGapValue00022 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00022_not_prime : ¬(recordGapCenter - 454054).Prime := by
  rw [fullRecordGapTerm00022_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00022, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00022_fast_pow_mod_ne_one

def fullRecordGapValue00023 : Nat := fullRecordGapCenterValue - 453982

theorem fullRecordGapTerm00023_eq_value :
    recordGapCenter - 453982 = fullRecordGapValue00023 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00023_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00023 (fullRecordGapValue00023 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00023_not_prime : ¬(recordGapCenter - 453982).Prime := by
  rw [fullRecordGapTerm00023_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00023, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00023_fast_pow_mod_ne_one

def fullRecordGapValue00024 : Nat := fullRecordGapCenterValue - 453954

theorem fullRecordGapTerm00024_eq_value :
    recordGapCenter - 453954 = fullRecordGapValue00024 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00024_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00024 (fullRecordGapValue00024 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00024_not_prime : ¬(recordGapCenter - 453954).Prime := by
  rw [fullRecordGapTerm00024_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00024, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00024_fast_pow_mod_ne_one

def fullRecordGapValue00025 : Nat := fullRecordGapCenterValue - 453802

theorem fullRecordGapTerm00025_eq_value :
    recordGapCenter - 453802 = fullRecordGapValue00025 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00025_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00025 (fullRecordGapValue00025 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00025_not_prime : ¬(recordGapCenter - 453802).Prime := by
  rw [fullRecordGapTerm00025_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00025, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00025_fast_pow_mod_ne_one

def fullRecordGapValue00026 : Nat := fullRecordGapCenterValue - 453448

theorem fullRecordGapTerm00026_eq_value :
    recordGapCenter - 453448 = fullRecordGapValue00026 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00026_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00026 (fullRecordGapValue00026 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00026_not_prime : ¬(recordGapCenter - 453448).Prime := by
  rw [fullRecordGapTerm00026_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00026, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00026_fast_pow_mod_ne_one

def fullRecordGapValue00027 : Nat := fullRecordGapCenterValue - 453318

theorem fullRecordGapTerm00027_eq_value :
    recordGapCenter - 453318 = fullRecordGapValue00027 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00027_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00027 (fullRecordGapValue00027 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00027_not_prime : ¬(recordGapCenter - 453318).Prime := by
  rw [fullRecordGapTerm00027_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00027, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00027_fast_pow_mod_ne_one

def fullRecordGapValue00028 : Nat := fullRecordGapCenterValue - 453234

theorem fullRecordGapTerm00028_eq_value :
    recordGapCenter - 453234 = fullRecordGapValue00028 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00028_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00028 (fullRecordGapValue00028 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00028_not_prime : ¬(recordGapCenter - 453234).Prime := by
  rw [fullRecordGapTerm00028_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00028, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00028_fast_pow_mod_ne_one

def fullRecordGapValue00029 : Nat := fullRecordGapCenterValue - 453198

theorem fullRecordGapTerm00029_eq_value :
    recordGapCenter - 453198 = fullRecordGapValue00029 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00029_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00029 (fullRecordGapValue00029 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00029_not_prime : ¬(recordGapCenter - 453198).Prime := by
  rw [fullRecordGapTerm00029_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00029, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00029_fast_pow_mod_ne_one

def fullRecordGapValue00030 : Nat := fullRecordGapCenterValue - 453162

theorem fullRecordGapTerm00030_eq_value :
    recordGapCenter - 453162 = fullRecordGapValue00030 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00030_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00030 (fullRecordGapValue00030 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00030_not_prime : ¬(recordGapCenter - 453162).Prime := by
  rw [fullRecordGapTerm00030_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00030, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00030_fast_pow_mod_ne_one

def fullRecordGapValue00031 : Nat := fullRecordGapCenterValue - 453148

theorem fullRecordGapTerm00031_eq_value :
    recordGapCenter - 453148 = fullRecordGapValue00031 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00031_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00031 (fullRecordGapValue00031 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00031_not_prime : ¬(recordGapCenter - 453148).Prime := by
  rw [fullRecordGapTerm00031_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00031, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00031_fast_pow_mod_ne_one

def fullRecordGapValue00032 : Nat := fullRecordGapCenterValue - 453018

theorem fullRecordGapTerm00032_eq_value :
    recordGapCenter - 453018 = fullRecordGapValue00032 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00032_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00032 (fullRecordGapValue00032 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00032_not_prime : ¬(recordGapCenter - 453018).Prime := by
  rw [fullRecordGapTerm00032_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00032, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00032_fast_pow_mod_ne_one

def fullRecordGapValue00033 : Nat := fullRecordGapCenterValue - 452932

theorem fullRecordGapTerm00033_eq_value :
    recordGapCenter - 452932 = fullRecordGapValue00033 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00033_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00033 (fullRecordGapValue00033 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00033_not_prime : ¬(recordGapCenter - 452932).Prime := by
  rw [fullRecordGapTerm00033_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00033, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00033_fast_pow_mod_ne_one

def fullRecordGapValue00034 : Nat := fullRecordGapCenterValue - 452668

theorem fullRecordGapTerm00034_eq_value :
    recordGapCenter - 452668 = fullRecordGapValue00034 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00034_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00034 (fullRecordGapValue00034 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00034_not_prime : ¬(recordGapCenter - 452668).Prime := by
  rw [fullRecordGapTerm00034_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00034, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00034_fast_pow_mod_ne_one

def fullRecordGapValue00035 : Nat := fullRecordGapCenterValue - 452644

theorem fullRecordGapTerm00035_eq_value :
    recordGapCenter - 452644 = fullRecordGapValue00035 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00035_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00035 (fullRecordGapValue00035 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00035_not_prime : ¬(recordGapCenter - 452644).Prime := by
  rw [fullRecordGapTerm00035_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00035, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00035_fast_pow_mod_ne_one

def fullRecordGapValue00036 : Nat := fullRecordGapCenterValue - 452442

theorem fullRecordGapTerm00036_eq_value :
    recordGapCenter - 452442 = fullRecordGapValue00036 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00036_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00036 (fullRecordGapValue00036 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00036_not_prime : ¬(recordGapCenter - 452442).Prime := by
  rw [fullRecordGapTerm00036_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00036, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00036_fast_pow_mod_ne_one

def fullRecordGapValue00037 : Nat := fullRecordGapCenterValue - 452344

theorem fullRecordGapTerm00037_eq_value :
    recordGapCenter - 452344 = fullRecordGapValue00037 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00037_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00037 (fullRecordGapValue00037 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00037_not_prime : ¬(recordGapCenter - 452344).Prime := by
  rw [fullRecordGapTerm00037_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00037, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00037_fast_pow_mod_ne_one

def fullRecordGapValue00038 : Nat := fullRecordGapCenterValue - 452262

theorem fullRecordGapTerm00038_eq_value :
    recordGapCenter - 452262 = fullRecordGapValue00038 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00038_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00038 (fullRecordGapValue00038 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00038_not_prime : ¬(recordGapCenter - 452262).Prime := by
  rw [fullRecordGapTerm00038_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00038, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00038_fast_pow_mod_ne_one

def fullRecordGapValue00039 : Nat := fullRecordGapCenterValue - 452248

theorem fullRecordGapTerm00039_eq_value :
    recordGapCenter - 452248 = fullRecordGapValue00039 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00039_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00039 (fullRecordGapValue00039 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00039_not_prime : ¬(recordGapCenter - 452248).Prime := by
  rw [fullRecordGapTerm00039_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00039, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00039_fast_pow_mod_ne_one

def fullRecordGapValue00040 : Nat := fullRecordGapCenterValue - 452044

theorem fullRecordGapTerm00040_eq_value :
    recordGapCenter - 452044 = fullRecordGapValue00040 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00040_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00040 (fullRecordGapValue00040 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00040_not_prime : ¬(recordGapCenter - 452044).Prime := by
  rw [fullRecordGapTerm00040_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00040, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00040_fast_pow_mod_ne_one

def fullRecordGapValue00041 : Nat := fullRecordGapCenterValue - 452002

theorem fullRecordGapTerm00041_eq_value :
    recordGapCenter - 452002 = fullRecordGapValue00041 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00041_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00041 (fullRecordGapValue00041 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00041_not_prime : ¬(recordGapCenter - 452002).Prime := by
  rw [fullRecordGapTerm00041_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00041, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00041_fast_pow_mod_ne_one

def fullRecordGapValue00042 : Nat := fullRecordGapCenterValue - 451978

theorem fullRecordGapTerm00042_eq_value :
    recordGapCenter - 451978 = fullRecordGapValue00042 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00042_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00042 (fullRecordGapValue00042 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00042_not_prime : ¬(recordGapCenter - 451978).Prime := by
  rw [fullRecordGapTerm00042_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00042, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00042_fast_pow_mod_ne_one

def fullRecordGapValue00043 : Nat := fullRecordGapCenterValue - 451842

theorem fullRecordGapTerm00043_eq_value :
    recordGapCenter - 451842 = fullRecordGapValue00043 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00043_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00043 (fullRecordGapValue00043 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00043_not_prime : ¬(recordGapCenter - 451842).Prime := by
  rw [fullRecordGapTerm00043_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00043, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00043_fast_pow_mod_ne_one

def fullRecordGapValue00044 : Nat := fullRecordGapCenterValue - 451810

theorem fullRecordGapTerm00044_eq_value :
    recordGapCenter - 451810 = fullRecordGapValue00044 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00044_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00044 (fullRecordGapValue00044 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00044_not_prime : ¬(recordGapCenter - 451810).Prime := by
  rw [fullRecordGapTerm00044_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00044, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00044_fast_pow_mod_ne_one

def fullRecordGapValue00045 : Nat := fullRecordGapCenterValue - 451734

theorem fullRecordGapTerm00045_eq_value :
    recordGapCenter - 451734 = fullRecordGapValue00045 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00045_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00045 (fullRecordGapValue00045 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00045_not_prime : ¬(recordGapCenter - 451734).Prime := by
  rw [fullRecordGapTerm00045_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00045, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00045_fast_pow_mod_ne_one

def fullRecordGapValue00046 : Nat := fullRecordGapCenterValue - 451678

theorem fullRecordGapTerm00046_eq_value :
    recordGapCenter - 451678 = fullRecordGapValue00046 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00046_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00046 (fullRecordGapValue00046 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00046_not_prime : ¬(recordGapCenter - 451678).Prime := by
  rw [fullRecordGapTerm00046_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00046, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00046_fast_pow_mod_ne_one

def fullRecordGapValue00047 : Nat := fullRecordGapCenterValue - 451614

theorem fullRecordGapTerm00047_eq_value :
    recordGapCenter - 451614 = fullRecordGapValue00047 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00047_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00047 (fullRecordGapValue00047 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00047_not_prime : ¬(recordGapCenter - 451614).Prime := by
  rw [fullRecordGapTerm00047_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00047, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00047_fast_pow_mod_ne_one

def fullRecordGapValue00048 : Nat := fullRecordGapCenterValue - 451534

theorem fullRecordGapTerm00048_eq_value :
    recordGapCenter - 451534 = fullRecordGapValue00048 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00048_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00048 (fullRecordGapValue00048 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00048_not_prime : ¬(recordGapCenter - 451534).Prime := by
  rw [fullRecordGapTerm00048_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00048, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00048_fast_pow_mod_ne_one

def fullRecordGapValue00049 : Nat := fullRecordGapCenterValue - 451372

theorem fullRecordGapTerm00049_eq_value :
    recordGapCenter - 451372 = fullRecordGapValue00049 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00049_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00049 (fullRecordGapValue00049 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00049_not_prime : ¬(recordGapCenter - 451372).Prime := by
  rw [fullRecordGapTerm00049_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00049, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00049_fast_pow_mod_ne_one

def fullRecordGapValue00050 : Nat := fullRecordGapCenterValue - 451342

theorem fullRecordGapTerm00050_eq_value :
    recordGapCenter - 451342 = fullRecordGapValue00050 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00050_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00050 (fullRecordGapValue00050 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00050_not_prime : ¬(recordGapCenter - 451342).Prime := by
  rw [fullRecordGapTerm00050_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00050, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00050_fast_pow_mod_ne_one

def fullRecordGapValue00051 : Nat := fullRecordGapCenterValue - 451302

theorem fullRecordGapTerm00051_eq_value :
    recordGapCenter - 451302 = fullRecordGapValue00051 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00051_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00051 (fullRecordGapValue00051 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00051_not_prime : ¬(recordGapCenter - 451302).Prime := by
  rw [fullRecordGapTerm00051_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00051, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00051_fast_pow_mod_ne_one

def fullRecordGapValue00052 : Nat := fullRecordGapCenterValue - 451258

theorem fullRecordGapTerm00052_eq_value :
    recordGapCenter - 451258 = fullRecordGapValue00052 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00052_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00052 (fullRecordGapValue00052 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00052_not_prime : ¬(recordGapCenter - 451258).Prime := by
  rw [fullRecordGapTerm00052_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00052, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00052_fast_pow_mod_ne_one

def fullRecordGapValue00053 : Nat := fullRecordGapCenterValue - 451254

theorem fullRecordGapTerm00053_eq_value :
    recordGapCenter - 451254 = fullRecordGapValue00053 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00053_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00053 (fullRecordGapValue00053 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00053_not_prime : ¬(recordGapCenter - 451254).Prime := by
  rw [fullRecordGapTerm00053_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00053, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00053_fast_pow_mod_ne_one

def fullRecordGapValue00054 : Nat := fullRecordGapCenterValue - 451138

theorem fullRecordGapTerm00054_eq_value :
    recordGapCenter - 451138 = fullRecordGapValue00054 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00054_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00054 (fullRecordGapValue00054 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00054_not_prime : ¬(recordGapCenter - 451138).Prime := by
  rw [fullRecordGapTerm00054_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00054, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00054_fast_pow_mod_ne_one

def fullRecordGapValue00055 : Nat := fullRecordGapCenterValue - 451054

theorem fullRecordGapTerm00055_eq_value :
    recordGapCenter - 451054 = fullRecordGapValue00055 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00055_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00055 (fullRecordGapValue00055 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00055_not_prime : ¬(recordGapCenter - 451054).Prime := by
  rw [fullRecordGapTerm00055_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00055, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00055_fast_pow_mod_ne_one

def fullRecordGapValue00056 : Nat := fullRecordGapCenterValue - 450958

theorem fullRecordGapTerm00056_eq_value :
    recordGapCenter - 450958 = fullRecordGapValue00056 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00056_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00056 (fullRecordGapValue00056 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00056_not_prime : ¬(recordGapCenter - 450958).Prime := by
  rw [fullRecordGapTerm00056_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00056, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00056_fast_pow_mod_ne_one

def fullRecordGapValue00057 : Nat := fullRecordGapCenterValue - 450922

theorem fullRecordGapTerm00057_eq_value :
    recordGapCenter - 450922 = fullRecordGapValue00057 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00057_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00057 (fullRecordGapValue00057 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00057_not_prime : ¬(recordGapCenter - 450922).Prime := by
  rw [fullRecordGapTerm00057_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00057, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00057_fast_pow_mod_ne_one

def fullRecordGapValue00058 : Nat := fullRecordGapCenterValue - 450798

theorem fullRecordGapTerm00058_eq_value :
    recordGapCenter - 450798 = fullRecordGapValue00058 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00058_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00058 (fullRecordGapValue00058 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00058_not_prime : ¬(recordGapCenter - 450798).Prime := by
  rw [fullRecordGapTerm00058_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00058, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00058_fast_pow_mod_ne_one

def fullRecordGapValue00059 : Nat := fullRecordGapCenterValue - 450742

theorem fullRecordGapTerm00059_eq_value :
    recordGapCenter - 450742 = fullRecordGapValue00059 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00059_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00059 (fullRecordGapValue00059 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00059_not_prime : ¬(recordGapCenter - 450742).Prime := by
  rw [fullRecordGapTerm00059_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00059, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00059_fast_pow_mod_ne_one

def fullRecordGapValue00060 : Nat := fullRecordGapCenterValue - 450628

theorem fullRecordGapTerm00060_eq_value :
    recordGapCenter - 450628 = fullRecordGapValue00060 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00060_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00060 (fullRecordGapValue00060 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00060_not_prime : ¬(recordGapCenter - 450628).Prime := by
  rw [fullRecordGapTerm00060_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00060, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00060_fast_pow_mod_ne_one

def fullRecordGapValue00061 : Nat := fullRecordGapCenterValue - 450610

theorem fullRecordGapTerm00061_eq_value :
    recordGapCenter - 450610 = fullRecordGapValue00061 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00061_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00061 (fullRecordGapValue00061 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00061_not_prime : ¬(recordGapCenter - 450610).Prime := by
  rw [fullRecordGapTerm00061_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00061, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00061_fast_pow_mod_ne_one

def fullRecordGapValue00062 : Nat := fullRecordGapCenterValue - 450442

theorem fullRecordGapTerm00062_eq_value :
    recordGapCenter - 450442 = fullRecordGapValue00062 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00062_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00062 (fullRecordGapValue00062 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00062_not_prime : ¬(recordGapCenter - 450442).Prime := by
  rw [fullRecordGapTerm00062_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00062, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00062_fast_pow_mod_ne_one

def fullRecordGapValue00063 : Nat := fullRecordGapCenterValue - 450412

theorem fullRecordGapTerm00063_eq_value :
    recordGapCenter - 450412 = fullRecordGapValue00063 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00063_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00063 (fullRecordGapValue00063 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00063_not_prime : ¬(recordGapCenter - 450412).Prime := by
  rw [fullRecordGapTerm00063_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00063, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00063_fast_pow_mod_ne_one

def fullRecordGapValue00064 : Nat := fullRecordGapCenterValue - 450298

theorem fullRecordGapTerm00064_eq_value :
    recordGapCenter - 450298 = fullRecordGapValue00064 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00064_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00064 (fullRecordGapValue00064 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00064_not_prime : ¬(recordGapCenter - 450298).Prime := by
  rw [fullRecordGapTerm00064_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00064, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00064_fast_pow_mod_ne_one

def fullRecordGapValue00065 : Nat := fullRecordGapCenterValue - 450292

theorem fullRecordGapTerm00065_eq_value :
    recordGapCenter - 450292 = fullRecordGapValue00065 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00065_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00065 (fullRecordGapValue00065 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00065_not_prime : ¬(recordGapCenter - 450292).Prime := by
  rw [fullRecordGapTerm00065_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00065, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00065_fast_pow_mod_ne_one

def fullRecordGapValue00066 : Nat := fullRecordGapCenterValue - 450174

theorem fullRecordGapTerm00066_eq_value :
    recordGapCenter - 450174 = fullRecordGapValue00066 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00066_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00066 (fullRecordGapValue00066 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00066_not_prime : ¬(recordGapCenter - 450174).Prime := by
  rw [fullRecordGapTerm00066_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00066, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00066_fast_pow_mod_ne_one

def fullRecordGapValue00067 : Nat := fullRecordGapCenterValue - 450154

theorem fullRecordGapTerm00067_eq_value :
    recordGapCenter - 450154 = fullRecordGapValue00067 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00067_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00067 (fullRecordGapValue00067 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00067_not_prime : ¬(recordGapCenter - 450154).Prime := by
  rw [fullRecordGapTerm00067_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00067, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00067_fast_pow_mod_ne_one

def fullRecordGapValue00068 : Nat := fullRecordGapCenterValue - 450130

theorem fullRecordGapTerm00068_eq_value :
    recordGapCenter - 450130 = fullRecordGapValue00068 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00068_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00068 (fullRecordGapValue00068 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00068_not_prime : ¬(recordGapCenter - 450130).Prime := by
  rw [fullRecordGapTerm00068_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00068, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00068_fast_pow_mod_ne_one

def fullRecordGapValue00069 : Nat := fullRecordGapCenterValue - 450078

theorem fullRecordGapTerm00069_eq_value :
    recordGapCenter - 450078 = fullRecordGapValue00069 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00069_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00069 (fullRecordGapValue00069 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00069_not_prime : ¬(recordGapCenter - 450078).Prime := by
  rw [fullRecordGapTerm00069_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00069, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00069_fast_pow_mod_ne_one

def fullRecordGapValue00070 : Nat := fullRecordGapCenterValue - 450004

theorem fullRecordGapTerm00070_eq_value :
    recordGapCenter - 450004 = fullRecordGapValue00070 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00070_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00070 (fullRecordGapValue00070 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00070_not_prime : ¬(recordGapCenter - 450004).Prime := by
  rw [fullRecordGapTerm00070_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00070, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00070_fast_pow_mod_ne_one

def fullRecordGapValue00071 : Nat := fullRecordGapCenterValue - 449782

theorem fullRecordGapTerm00071_eq_value :
    recordGapCenter - 449782 = fullRecordGapValue00071 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00071_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00071 (fullRecordGapValue00071 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00071_not_prime : ¬(recordGapCenter - 449782).Prime := by
  rw [fullRecordGapTerm00071_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00071, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00071_fast_pow_mod_ne_one

def fullRecordGapValue00072 : Nat := fullRecordGapCenterValue - 449710

theorem fullRecordGapTerm00072_eq_value :
    recordGapCenter - 449710 = fullRecordGapValue00072 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00072_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00072 (fullRecordGapValue00072 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00072_not_prime : ¬(recordGapCenter - 449710).Prime := by
  rw [fullRecordGapTerm00072_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00072, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00072_fast_pow_mod_ne_one

def fullRecordGapValue00073 : Nat := fullRecordGapCenterValue - 449518

theorem fullRecordGapTerm00073_eq_value :
    recordGapCenter - 449518 = fullRecordGapValue00073 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00073_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00073 (fullRecordGapValue00073 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00073_not_prime : ¬(recordGapCenter - 449518).Prime := by
  rw [fullRecordGapTerm00073_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00073, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00073_fast_pow_mod_ne_one

def fullRecordGapValue00074 : Nat := fullRecordGapCenterValue - 449368

theorem fullRecordGapTerm00074_eq_value :
    recordGapCenter - 449368 = fullRecordGapValue00074 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00074_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00074 (fullRecordGapValue00074 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00074_not_prime : ¬(recordGapCenter - 449368).Prime := by
  rw [fullRecordGapTerm00074_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00074, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00074_fast_pow_mod_ne_one

def fullRecordGapValue00075 : Nat := fullRecordGapCenterValue - 449188

theorem fullRecordGapTerm00075_eq_value :
    recordGapCenter - 449188 = fullRecordGapValue00075 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00075_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00075 (fullRecordGapValue00075 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00075_not_prime : ¬(recordGapCenter - 449188).Prime := by
  rw [fullRecordGapTerm00075_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00075, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00075_fast_pow_mod_ne_one

def fullRecordGapValue00076 : Nat := fullRecordGapCenterValue - 448984

theorem fullRecordGapTerm00076_eq_value :
    recordGapCenter - 448984 = fullRecordGapValue00076 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00076_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00076 (fullRecordGapValue00076 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00076_not_prime : ¬(recordGapCenter - 448984).Prime := by
  rw [fullRecordGapTerm00076_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00076, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00076_fast_pow_mod_ne_one

def fullRecordGapValue00077 : Nat := fullRecordGapCenterValue - 448962

theorem fullRecordGapTerm00077_eq_value :
    recordGapCenter - 448962 = fullRecordGapValue00077 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00077_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00077 (fullRecordGapValue00077 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00077_not_prime : ¬(recordGapCenter - 448962).Prime := by
  rw [fullRecordGapTerm00077_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00077, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00077_fast_pow_mod_ne_one

def fullRecordGapValue00078 : Nat := fullRecordGapCenterValue - 448852

theorem fullRecordGapTerm00078_eq_value :
    recordGapCenter - 448852 = fullRecordGapValue00078 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00078_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00078 (fullRecordGapValue00078 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00078_not_prime : ¬(recordGapCenter - 448852).Prime := by
  rw [fullRecordGapTerm00078_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00078, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00078_fast_pow_mod_ne_one

def fullRecordGapValue00079 : Nat := fullRecordGapCenterValue - 448828

theorem fullRecordGapTerm00079_eq_value :
    recordGapCenter - 448828 = fullRecordGapValue00079 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00079_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00079 (fullRecordGapValue00079 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00079_not_prime : ¬(recordGapCenter - 448828).Prime := by
  rw [fullRecordGapTerm00079_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00079, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00079_fast_pow_mod_ne_one

def fullRecordGapValue00080 : Nat := fullRecordGapCenterValue - 448648

theorem fullRecordGapTerm00080_eq_value :
    recordGapCenter - 448648 = fullRecordGapValue00080 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00080_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00080 (fullRecordGapValue00080 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00080_not_prime : ¬(recordGapCenter - 448648).Prime := by
  rw [fullRecordGapTerm00080_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00080, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00080_fast_pow_mod_ne_one

def fullRecordGapValue00081 : Nat := fullRecordGapCenterValue - 448534

theorem fullRecordGapTerm00081_eq_value :
    recordGapCenter - 448534 = fullRecordGapValue00081 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00081_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00081 (fullRecordGapValue00081 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00081_not_prime : ¬(recordGapCenter - 448534).Prime := by
  rw [fullRecordGapTerm00081_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00081, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00081_fast_pow_mod_ne_one

def fullRecordGapValue00082 : Nat := fullRecordGapCenterValue - 448444

theorem fullRecordGapTerm00082_eq_value :
    recordGapCenter - 448444 = fullRecordGapValue00082 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00082_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00082 (fullRecordGapValue00082 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00082_not_prime : ¬(recordGapCenter - 448444).Prime := by
  rw [fullRecordGapTerm00082_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00082, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00082_fast_pow_mod_ne_one

def fullRecordGapValue00083 : Nat := fullRecordGapCenterValue - 448348

theorem fullRecordGapTerm00083_eq_value :
    recordGapCenter - 448348 = fullRecordGapValue00083 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00083_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00083 (fullRecordGapValue00083 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00083_not_prime : ¬(recordGapCenter - 448348).Prime := by
  rw [fullRecordGapTerm00083_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00083, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00083_fast_pow_mod_ne_one

def fullRecordGapValue00084 : Nat := fullRecordGapCenterValue - 448278

theorem fullRecordGapTerm00084_eq_value :
    recordGapCenter - 448278 = fullRecordGapValue00084 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00084_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00084 (fullRecordGapValue00084 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00084_not_prime : ¬(recordGapCenter - 448278).Prime := by
  rw [fullRecordGapTerm00084_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00084, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00084_fast_pow_mod_ne_one

def fullRecordGapValue00085 : Nat := fullRecordGapCenterValue - 448258

theorem fullRecordGapTerm00085_eq_value :
    recordGapCenter - 448258 = fullRecordGapValue00085 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00085_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00085 (fullRecordGapValue00085 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00085_not_prime : ¬(recordGapCenter - 448258).Prime := by
  rw [fullRecordGapTerm00085_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00085, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00085_fast_pow_mod_ne_one

def fullRecordGapValue00086 : Nat := fullRecordGapCenterValue - 448138

theorem fullRecordGapTerm00086_eq_value :
    recordGapCenter - 448138 = fullRecordGapValue00086 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00086_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00086 (fullRecordGapValue00086 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00086_not_prime : ¬(recordGapCenter - 448138).Prime := by
  rw [fullRecordGapTerm00086_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00086, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00086_fast_pow_mod_ne_one

def fullRecordGapValue00087 : Nat := fullRecordGapCenterValue - 448072

theorem fullRecordGapTerm00087_eq_value :
    recordGapCenter - 448072 = fullRecordGapValue00087 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00087_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00087 (fullRecordGapValue00087 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00087_not_prime : ¬(recordGapCenter - 448072).Prime := by
  rw [fullRecordGapTerm00087_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00087, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00087_fast_pow_mod_ne_one

def fullRecordGapValue00088 : Nat := fullRecordGapCenterValue - 448054

theorem fullRecordGapTerm00088_eq_value :
    recordGapCenter - 448054 = fullRecordGapValue00088 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00088_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00088 (fullRecordGapValue00088 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00088_not_prime : ¬(recordGapCenter - 448054).Prime := by
  rw [fullRecordGapTerm00088_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00088, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00088_fast_pow_mod_ne_one

def fullRecordGapValue00089 : Nat := fullRecordGapCenterValue - 447970

theorem fullRecordGapTerm00089_eq_value :
    recordGapCenter - 447970 = fullRecordGapValue00089 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00089_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00089 (fullRecordGapValue00089 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00089_not_prime : ¬(recordGapCenter - 447970).Prime := by
  rw [fullRecordGapTerm00089_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00089, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00089_fast_pow_mod_ne_one

def fullRecordGapValue00090 : Nat := fullRecordGapCenterValue - 447838

theorem fullRecordGapTerm00090_eq_value :
    recordGapCenter - 447838 = fullRecordGapValue00090 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00090_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00090 (fullRecordGapValue00090 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00090_not_prime : ¬(recordGapCenter - 447838).Prime := by
  rw [fullRecordGapTerm00090_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00090, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00090_fast_pow_mod_ne_one

def fullRecordGapValue00091 : Nat := fullRecordGapCenterValue - 447730

theorem fullRecordGapTerm00091_eq_value :
    recordGapCenter - 447730 = fullRecordGapValue00091 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00091_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00091 (fullRecordGapValue00091 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00091_not_prime : ¬(recordGapCenter - 447730).Prime := by
  rw [fullRecordGapTerm00091_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00091, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00091_fast_pow_mod_ne_one

def fullRecordGapValue00092 : Nat := fullRecordGapCenterValue - 447652

theorem fullRecordGapTerm00092_eq_value :
    recordGapCenter - 447652 = fullRecordGapValue00092 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00092_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00092 (fullRecordGapValue00092 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00092_not_prime : ¬(recordGapCenter - 447652).Prime := by
  rw [fullRecordGapTerm00092_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00092, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00092_fast_pow_mod_ne_one

def fullRecordGapValue00093 : Nat := fullRecordGapCenterValue - 447592

theorem fullRecordGapTerm00093_eq_value :
    recordGapCenter - 447592 = fullRecordGapValue00093 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00093_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00093 (fullRecordGapValue00093 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00093_not_prime : ¬(recordGapCenter - 447592).Prime := by
  rw [fullRecordGapTerm00093_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00093, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00093_fast_pow_mod_ne_one

def fullRecordGapValue00094 : Nat := fullRecordGapCenterValue - 447514

theorem fullRecordGapTerm00094_eq_value :
    recordGapCenter - 447514 = fullRecordGapValue00094 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00094_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00094 (fullRecordGapValue00094 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00094_not_prime : ¬(recordGapCenter - 447514).Prime := by
  rw [fullRecordGapTerm00094_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00094, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00094_fast_pow_mod_ne_one

def fullRecordGapValue00095 : Nat := fullRecordGapCenterValue - 447394

theorem fullRecordGapTerm00095_eq_value :
    recordGapCenter - 447394 = fullRecordGapValue00095 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00095_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00095 (fullRecordGapValue00095 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00095_not_prime : ¬(recordGapCenter - 447394).Prime := by
  rw [fullRecordGapTerm00095_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00095, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00095_fast_pow_mod_ne_one

def fullRecordGapValue00096 : Nat := fullRecordGapCenterValue - 447334

theorem fullRecordGapTerm00096_eq_value :
    recordGapCenter - 447334 = fullRecordGapValue00096 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00096_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00096 (fullRecordGapValue00096 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00096_not_prime : ¬(recordGapCenter - 447334).Prime := by
  rw [fullRecordGapTerm00096_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00096, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00096_fast_pow_mod_ne_one

def fullRecordGapValue00097 : Nat := fullRecordGapCenterValue - 447208

theorem fullRecordGapTerm00097_eq_value :
    recordGapCenter - 447208 = fullRecordGapValue00097 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00097_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00097 (fullRecordGapValue00097 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00097_not_prime : ¬(recordGapCenter - 447208).Prime := by
  rw [fullRecordGapTerm00097_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00097, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00097_fast_pow_mod_ne_one

def fullRecordGapValue00098 : Nat := fullRecordGapCenterValue - 447058

theorem fullRecordGapTerm00098_eq_value :
    recordGapCenter - 447058 = fullRecordGapValue00098 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00098_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00098 (fullRecordGapValue00098 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00098_not_prime : ¬(recordGapCenter - 447058).Prime := by
  rw [fullRecordGapTerm00098_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00098, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00098_fast_pow_mod_ne_one

def fullRecordGapValue00099 : Nat := fullRecordGapCenterValue - 447054

theorem fullRecordGapTerm00099_eq_value :
    recordGapCenter - 447054 = fullRecordGapValue00099 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00099_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00099 (fullRecordGapValue00099 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00099_not_prime : ¬(recordGapCenter - 447054).Prime := by
  rw [fullRecordGapTerm00099_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00099, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00099_fast_pow_mod_ne_one

def fullRecordGapValue00100 : Nat := fullRecordGapCenterValue - 446968

theorem fullRecordGapTerm00100_eq_value :
    recordGapCenter - 446968 = fullRecordGapValue00100 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00100_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00100 (fullRecordGapValue00100 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00100_not_prime : ¬(recordGapCenter - 446968).Prime := by
  rw [fullRecordGapTerm00100_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00100, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00100_fast_pow_mod_ne_one

def fullRecordGapValue00101 : Nat := fullRecordGapCenterValue - 446962

theorem fullRecordGapTerm00101_eq_value :
    recordGapCenter - 446962 = fullRecordGapValue00101 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00101_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00101 (fullRecordGapValue00101 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00101_not_prime : ¬(recordGapCenter - 446962).Prime := by
  rw [fullRecordGapTerm00101_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00101, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00101_fast_pow_mod_ne_one

def fullRecordGapValue00102 : Nat := fullRecordGapCenterValue - 446938

theorem fullRecordGapTerm00102_eq_value :
    recordGapCenter - 446938 = fullRecordGapValue00102 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00102_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00102 (fullRecordGapValue00102 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00102_not_prime : ¬(recordGapCenter - 446938).Prime := by
  rw [fullRecordGapTerm00102_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00102, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00102_fast_pow_mod_ne_one

def fullRecordGapValue00103 : Nat := fullRecordGapCenterValue - 446932

theorem fullRecordGapTerm00103_eq_value :
    recordGapCenter - 446932 = fullRecordGapValue00103 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00103_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00103 (fullRecordGapValue00103 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00103_not_prime : ¬(recordGapCenter - 446932).Prime := by
  rw [fullRecordGapTerm00103_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00103, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00103_fast_pow_mod_ne_one

def fullRecordGapValue00104 : Nat := fullRecordGapCenterValue - 446878

theorem fullRecordGapTerm00104_eq_value :
    recordGapCenter - 446878 = fullRecordGapValue00104 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00104_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00104 (fullRecordGapValue00104 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00104_not_prime : ¬(recordGapCenter - 446878).Prime := by
  rw [fullRecordGapTerm00104_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00104, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00104_fast_pow_mod_ne_one

def fullRecordGapValue00105 : Nat := fullRecordGapCenterValue - 446722

theorem fullRecordGapTerm00105_eq_value :
    recordGapCenter - 446722 = fullRecordGapValue00105 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00105_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00105 (fullRecordGapValue00105 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00105_not_prime : ¬(recordGapCenter - 446722).Prime := by
  rw [fullRecordGapTerm00105_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00105, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00105_fast_pow_mod_ne_one

def fullRecordGapValue00106 : Nat := fullRecordGapCenterValue - 446718

theorem fullRecordGapTerm00106_eq_value :
    recordGapCenter - 446718 = fullRecordGapValue00106 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00106_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00106 (fullRecordGapValue00106 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00106_not_prime : ¬(recordGapCenter - 446718).Prime := by
  rw [fullRecordGapTerm00106_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00106, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00106_fast_pow_mod_ne_one

def fullRecordGapValue00107 : Nat := fullRecordGapCenterValue - 446694

theorem fullRecordGapTerm00107_eq_value :
    recordGapCenter - 446694 = fullRecordGapValue00107 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00107_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00107 (fullRecordGapValue00107 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00107_not_prime : ¬(recordGapCenter - 446694).Prime := by
  rw [fullRecordGapTerm00107_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00107, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00107_fast_pow_mod_ne_one

def fullRecordGapValue00108 : Nat := fullRecordGapCenterValue - 446518

theorem fullRecordGapTerm00108_eq_value :
    recordGapCenter - 446518 = fullRecordGapValue00108 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00108_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00108 (fullRecordGapValue00108 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00108_not_prime : ¬(recordGapCenter - 446518).Prime := by
  rw [fullRecordGapTerm00108_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00108, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00108_fast_pow_mod_ne_one

def fullRecordGapValue00109 : Nat := fullRecordGapCenterValue - 446308

theorem fullRecordGapTerm00109_eq_value :
    recordGapCenter - 446308 = fullRecordGapValue00109 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00109_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00109 (fullRecordGapValue00109 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00109_not_prime : ¬(recordGapCenter - 446308).Prime := by
  rw [fullRecordGapTerm00109_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00109, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00109_fast_pow_mod_ne_one

def fullRecordGapValue00110 : Nat := fullRecordGapCenterValue - 446122

theorem fullRecordGapTerm00110_eq_value :
    recordGapCenter - 446122 = fullRecordGapValue00110 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00110_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00110 (fullRecordGapValue00110 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00110_not_prime : ¬(recordGapCenter - 446122).Prime := by
  rw [fullRecordGapTerm00110_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00110, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00110_fast_pow_mod_ne_one

def fullRecordGapValue00111 : Nat := fullRecordGapCenterValue - 446074

theorem fullRecordGapTerm00111_eq_value :
    recordGapCenter - 446074 = fullRecordGapValue00111 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00111_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00111 (fullRecordGapValue00111 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00111_not_prime : ¬(recordGapCenter - 446074).Prime := by
  rw [fullRecordGapTerm00111_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00111, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00111_fast_pow_mod_ne_one

def fullRecordGapValue00112 : Nat := fullRecordGapCenterValue - 446038

theorem fullRecordGapTerm00112_eq_value :
    recordGapCenter - 446038 = fullRecordGapValue00112 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00112_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00112 (fullRecordGapValue00112 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00112_not_prime : ¬(recordGapCenter - 446038).Prime := by
  rw [fullRecordGapTerm00112_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00112, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00112_fast_pow_mod_ne_one

def fullRecordGapValue00113 : Nat := fullRecordGapCenterValue - 445948

theorem fullRecordGapTerm00113_eq_value :
    recordGapCenter - 445948 = fullRecordGapValue00113 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00113_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00113 (fullRecordGapValue00113 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00113_not_prime : ¬(recordGapCenter - 445948).Prime := by
  rw [fullRecordGapTerm00113_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00113, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00113_fast_pow_mod_ne_one

def fullRecordGapValue00114 : Nat := fullRecordGapCenterValue - 445870

theorem fullRecordGapTerm00114_eq_value :
    recordGapCenter - 445870 = fullRecordGapValue00114 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00114_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00114 (fullRecordGapValue00114 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00114_not_prime : ¬(recordGapCenter - 445870).Prime := by
  rw [fullRecordGapTerm00114_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00114, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00114_fast_pow_mod_ne_one

def fullRecordGapValue00115 : Nat := fullRecordGapCenterValue - 445864

theorem fullRecordGapTerm00115_eq_value :
    recordGapCenter - 445864 = fullRecordGapValue00115 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00115_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00115 (fullRecordGapValue00115 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00115_not_prime : ¬(recordGapCenter - 445864).Prime := by
  rw [fullRecordGapTerm00115_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00115, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00115_fast_pow_mod_ne_one

def fullRecordGapValue00116 : Nat := fullRecordGapCenterValue - 445722

theorem fullRecordGapTerm00116_eq_value :
    recordGapCenter - 445722 = fullRecordGapValue00116 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00116_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00116 (fullRecordGapValue00116 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00116_not_prime : ¬(recordGapCenter - 445722).Prime := by
  rw [fullRecordGapTerm00116_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00116, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00116_fast_pow_mod_ne_one

def fullRecordGapValue00117 : Nat := fullRecordGapCenterValue - 445674

theorem fullRecordGapTerm00117_eq_value :
    recordGapCenter - 445674 = fullRecordGapValue00117 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00117_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00117 (fullRecordGapValue00117 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00117_not_prime : ¬(recordGapCenter - 445674).Prime := by
  rw [fullRecordGapTerm00117_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00117, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00117_fast_pow_mod_ne_one

def fullRecordGapValue00118 : Nat := fullRecordGapCenterValue - 445630

theorem fullRecordGapTerm00118_eq_value :
    recordGapCenter - 445630 = fullRecordGapValue00118 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00118_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00118 (fullRecordGapValue00118 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00118_not_prime : ¬(recordGapCenter - 445630).Prime := by
  rw [fullRecordGapTerm00118_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00118, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00118_fast_pow_mod_ne_one

def fullRecordGapValue00119 : Nat := fullRecordGapCenterValue - 445528

theorem fullRecordGapTerm00119_eq_value :
    recordGapCenter - 445528 = fullRecordGapValue00119 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00119_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00119 (fullRecordGapValue00119 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00119_not_prime : ¬(recordGapCenter - 445528).Prime := by
  rw [fullRecordGapTerm00119_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00119, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00119_fast_pow_mod_ne_one

def fullRecordGapValue00120 : Nat := fullRecordGapCenterValue - 445500

theorem fullRecordGapTerm00120_eq_value :
    recordGapCenter - 445500 = fullRecordGapValue00120 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00120_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00120 (fullRecordGapValue00120 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00120_not_prime : ¬(recordGapCenter - 445500).Prime := by
  rw [fullRecordGapTerm00120_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00120, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00120_fast_pow_mod_ne_one

def fullRecordGapValue00121 : Nat := fullRecordGapCenterValue - 445330

theorem fullRecordGapTerm00121_eq_value :
    recordGapCenter - 445330 = fullRecordGapValue00121 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00121_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00121 (fullRecordGapValue00121 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00121_not_prime : ¬(recordGapCenter - 445330).Prime := by
  rw [fullRecordGapTerm00121_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00121, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00121_fast_pow_mod_ne_one

def fullRecordGapValue00122 : Nat := fullRecordGapCenterValue - 445318

theorem fullRecordGapTerm00122_eq_value :
    recordGapCenter - 445318 = fullRecordGapValue00122 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00122_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00122 (fullRecordGapValue00122 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00122_not_prime : ¬(recordGapCenter - 445318).Prime := by
  rw [fullRecordGapTerm00122_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00122, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00122_fast_pow_mod_ne_one

def fullRecordGapValue00123 : Nat := fullRecordGapCenterValue - 445294

theorem fullRecordGapTerm00123_eq_value :
    recordGapCenter - 445294 = fullRecordGapValue00123 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00123_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00123 (fullRecordGapValue00123 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00123_not_prime : ¬(recordGapCenter - 445294).Prime := by
  rw [fullRecordGapTerm00123_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00123, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00123_fast_pow_mod_ne_one

def fullRecordGapValue00124 : Nat := fullRecordGapCenterValue - 445288

theorem fullRecordGapTerm00124_eq_value :
    recordGapCenter - 445288 = fullRecordGapValue00124 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00124_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00124 (fullRecordGapValue00124 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00124_not_prime : ¬(recordGapCenter - 445288).Prime := by
  rw [fullRecordGapTerm00124_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00124, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00124_fast_pow_mod_ne_one

def fullRecordGapValue00125 : Nat := fullRecordGapCenterValue - 445182

theorem fullRecordGapTerm00125_eq_value :
    recordGapCenter - 445182 = fullRecordGapValue00125 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00125_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00125 (fullRecordGapValue00125 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00125_not_prime : ¬(recordGapCenter - 445182).Prime := by
  rw [fullRecordGapTerm00125_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00125, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00125_fast_pow_mod_ne_one

def fullRecordGapValue00126 : Nat := fullRecordGapCenterValue - 445062

theorem fullRecordGapTerm00126_eq_value :
    recordGapCenter - 445062 = fullRecordGapValue00126 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00126_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00126 (fullRecordGapValue00126 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00126_not_prime : ¬(recordGapCenter - 445062).Prime := by
  rw [fullRecordGapTerm00126_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00126, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00126_fast_pow_mod_ne_one

def fullRecordGapValue00127 : Nat := fullRecordGapCenterValue - 445002

theorem fullRecordGapTerm00127_eq_value :
    recordGapCenter - 445002 = fullRecordGapValue00127 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00127_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00127 (fullRecordGapValue00127 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00127_not_prime : ¬(recordGapCenter - 445002).Prime := by
  rw [fullRecordGapTerm00127_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00127, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00127_fast_pow_mod_ne_one

def fullRecordGapValue00128 : Nat := fullRecordGapCenterValue - 444922

theorem fullRecordGapTerm00128_eq_value :
    recordGapCenter - 444922 = fullRecordGapValue00128 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00128_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00128 (fullRecordGapValue00128 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00128_not_prime : ¬(recordGapCenter - 444922).Prime := by
  rw [fullRecordGapTerm00128_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00128, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00128_fast_pow_mod_ne_one

def fullRecordGapValue00129 : Nat := fullRecordGapCenterValue - 444838

theorem fullRecordGapTerm00129_eq_value :
    recordGapCenter - 444838 = fullRecordGapValue00129 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00129_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00129 (fullRecordGapValue00129 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00129_not_prime : ¬(recordGapCenter - 444838).Prime := by
  rw [fullRecordGapTerm00129_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00129, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00129_fast_pow_mod_ne_one

def fullRecordGapValue00130 : Nat := fullRecordGapCenterValue - 444658

theorem fullRecordGapTerm00130_eq_value :
    recordGapCenter - 444658 = fullRecordGapValue00130 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00130_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00130 (fullRecordGapValue00130 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00130_not_prime : ¬(recordGapCenter - 444658).Prime := by
  rw [fullRecordGapTerm00130_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00130, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00130_fast_pow_mod_ne_one

def fullRecordGapValue00131 : Nat := fullRecordGapCenterValue - 444622

theorem fullRecordGapTerm00131_eq_value :
    recordGapCenter - 444622 = fullRecordGapValue00131 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00131_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00131 (fullRecordGapValue00131 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00131_not_prime : ¬(recordGapCenter - 444622).Prime := by
  rw [fullRecordGapTerm00131_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00131, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00131_fast_pow_mod_ne_one

def fullRecordGapValue00132 : Nat := fullRecordGapCenterValue - 444594

theorem fullRecordGapTerm00132_eq_value :
    recordGapCenter - 444594 = fullRecordGapValue00132 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00132_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00132 (fullRecordGapValue00132 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00132_not_prime : ¬(recordGapCenter - 444594).Prime := by
  rw [fullRecordGapTerm00132_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00132, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00132_fast_pow_mod_ne_one

def fullRecordGapValue00133 : Nat := fullRecordGapCenterValue - 444538

theorem fullRecordGapTerm00133_eq_value :
    recordGapCenter - 444538 = fullRecordGapValue00133 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00133_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00133 (fullRecordGapValue00133 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00133_not_prime : ¬(recordGapCenter - 444538).Prime := by
  rw [fullRecordGapTerm00133_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00133, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00133_fast_pow_mod_ne_one

def fullRecordGapValue00134 : Nat := fullRecordGapCenterValue - 444484

theorem fullRecordGapTerm00134_eq_value :
    recordGapCenter - 444484 = fullRecordGapValue00134 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00134_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00134 (fullRecordGapValue00134 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00134_not_prime : ¬(recordGapCenter - 444484).Prime := by
  rw [fullRecordGapTerm00134_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00134, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00134_fast_pow_mod_ne_one

def fullRecordGapValue00135 : Nat := fullRecordGapCenterValue - 444364

theorem fullRecordGapTerm00135_eq_value :
    recordGapCenter - 444364 = fullRecordGapValue00135 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00135_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00135 (fullRecordGapValue00135 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00135_not_prime : ¬(recordGapCenter - 444364).Prime := by
  rw [fullRecordGapTerm00135_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00135, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00135_fast_pow_mod_ne_one

def fullRecordGapValue00136 : Nat := fullRecordGapCenterValue - 444322

theorem fullRecordGapTerm00136_eq_value :
    recordGapCenter - 444322 = fullRecordGapValue00136 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00136_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00136 (fullRecordGapValue00136 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00136_not_prime : ¬(recordGapCenter - 444322).Prime := by
  rw [fullRecordGapTerm00136_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00136, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00136_fast_pow_mod_ne_one

def fullRecordGapValue00137 : Nat := fullRecordGapCenterValue - 444282

theorem fullRecordGapTerm00137_eq_value :
    recordGapCenter - 444282 = fullRecordGapValue00137 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00137_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00137 (fullRecordGapValue00137 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00137_not_prime : ¬(recordGapCenter - 444282).Prime := by
  rw [fullRecordGapTerm00137_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00137, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00137_fast_pow_mod_ne_one

def fullRecordGapValue00138 : Nat := fullRecordGapCenterValue - 444232

theorem fullRecordGapTerm00138_eq_value :
    recordGapCenter - 444232 = fullRecordGapValue00138 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00138_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00138 (fullRecordGapValue00138 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00138_not_prime : ¬(recordGapCenter - 444232).Prime := by
  rw [fullRecordGapTerm00138_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00138, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00138_fast_pow_mod_ne_one

def fullRecordGapValue00139 : Nat := fullRecordGapCenterValue - 444124

theorem fullRecordGapTerm00139_eq_value :
    recordGapCenter - 444124 = fullRecordGapValue00139 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00139_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00139 (fullRecordGapValue00139 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00139_not_prime : ¬(recordGapCenter - 444124).Prime := by
  rw [fullRecordGapTerm00139_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00139, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00139_fast_pow_mod_ne_one

def fullRecordGapValue00140 : Nat := fullRecordGapCenterValue - 443974

theorem fullRecordGapTerm00140_eq_value :
    recordGapCenter - 443974 = fullRecordGapValue00140 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00140_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00140 (fullRecordGapValue00140 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00140_not_prime : ¬(recordGapCenter - 443974).Prime := by
  rw [fullRecordGapTerm00140_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00140, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00140_fast_pow_mod_ne_one

def fullRecordGapValue00141 : Nat := fullRecordGapCenterValue - 443914

theorem fullRecordGapTerm00141_eq_value :
    recordGapCenter - 443914 = fullRecordGapValue00141 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00141_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00141 (fullRecordGapValue00141 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00141_not_prime : ¬(recordGapCenter - 443914).Prime := by
  rw [fullRecordGapTerm00141_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00141, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00141_fast_pow_mod_ne_one

def fullRecordGapValue00142 : Nat := fullRecordGapCenterValue - 443838

theorem fullRecordGapTerm00142_eq_value :
    recordGapCenter - 443838 = fullRecordGapValue00142 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00142_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00142 (fullRecordGapValue00142 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00142_not_prime : ¬(recordGapCenter - 443838).Prime := by
  rw [fullRecordGapTerm00142_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00142, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00142_fast_pow_mod_ne_one

def fullRecordGapValue00143 : Nat := fullRecordGapCenterValue - 443830

theorem fullRecordGapTerm00143_eq_value :
    recordGapCenter - 443830 = fullRecordGapValue00143 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00143_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00143 (fullRecordGapValue00143 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00143_not_prime : ¬(recordGapCenter - 443830).Prime := by
  rw [fullRecordGapTerm00143_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00143, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00143_fast_pow_mod_ne_one

def fullRecordGapValue00144 : Nat := fullRecordGapCenterValue - 443782

theorem fullRecordGapTerm00144_eq_value :
    recordGapCenter - 443782 = fullRecordGapValue00144 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00144_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00144 (fullRecordGapValue00144 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00144_not_prime : ¬(recordGapCenter - 443782).Prime := by
  rw [fullRecordGapTerm00144_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00144, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00144_fast_pow_mod_ne_one

def fullRecordGapValue00145 : Nat := fullRecordGapCenterValue - 443658

theorem fullRecordGapTerm00145_eq_value :
    recordGapCenter - 443658 = fullRecordGapValue00145 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00145_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00145 (fullRecordGapValue00145 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00145_not_prime : ¬(recordGapCenter - 443658).Prime := by
  rw [fullRecordGapTerm00145_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00145, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00145_fast_pow_mod_ne_one

def fullRecordGapValue00146 : Nat := fullRecordGapCenterValue - 443614

theorem fullRecordGapTerm00146_eq_value :
    recordGapCenter - 443614 = fullRecordGapValue00146 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00146_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00146 (fullRecordGapValue00146 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00146_not_prime : ¬(recordGapCenter - 443614).Prime := by
  rw [fullRecordGapTerm00146_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00146, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00146_fast_pow_mod_ne_one

def fullRecordGapValue00147 : Nat := fullRecordGapCenterValue - 443512

theorem fullRecordGapTerm00147_eq_value :
    recordGapCenter - 443512 = fullRecordGapValue00147 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00147_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00147 (fullRecordGapValue00147 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00147_not_prime : ¬(recordGapCenter - 443512).Prime := by
  rw [fullRecordGapTerm00147_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00147, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00147_fast_pow_mod_ne_one

def fullRecordGapValue00148 : Nat := fullRecordGapCenterValue - 443494

theorem fullRecordGapTerm00148_eq_value :
    recordGapCenter - 443494 = fullRecordGapValue00148 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00148_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00148 (fullRecordGapValue00148 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00148_not_prime : ¬(recordGapCenter - 443494).Prime := by
  rw [fullRecordGapTerm00148_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00148, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00148_fast_pow_mod_ne_one

def fullRecordGapValue00149 : Nat := fullRecordGapCenterValue - 443442

theorem fullRecordGapTerm00149_eq_value :
    recordGapCenter - 443442 = fullRecordGapValue00149 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00149_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00149 (fullRecordGapValue00149 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00149_not_prime : ¬(recordGapCenter - 443442).Prime := by
  rw [fullRecordGapTerm00149_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00149, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00149_fast_pow_mod_ne_one

def fullRecordGapValue00150 : Nat := fullRecordGapCenterValue - 443298

theorem fullRecordGapTerm00150_eq_value :
    recordGapCenter - 443298 = fullRecordGapValue00150 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00150_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00150 (fullRecordGapValue00150 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00150_not_prime : ¬(recordGapCenter - 443298).Prime := by
  rw [fullRecordGapTerm00150_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00150, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00150_fast_pow_mod_ne_one

def fullRecordGapValue00151 : Nat := fullRecordGapCenterValue - 443284

theorem fullRecordGapTerm00151_eq_value :
    recordGapCenter - 443284 = fullRecordGapValue00151 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00151_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00151 (fullRecordGapValue00151 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00151_not_prime : ¬(recordGapCenter - 443284).Prime := by
  rw [fullRecordGapTerm00151_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00151, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00151_fast_pow_mod_ne_one

def fullRecordGapValue00152 : Nat := fullRecordGapCenterValue - 443202

theorem fullRecordGapTerm00152_eq_value :
    recordGapCenter - 443202 = fullRecordGapValue00152 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00152_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00152 (fullRecordGapValue00152 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00152_not_prime : ¬(recordGapCenter - 443202).Prime := by
  rw [fullRecordGapTerm00152_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00152, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00152_fast_pow_mod_ne_one

def fullRecordGapValue00153 : Nat := fullRecordGapCenterValue - 443134

theorem fullRecordGapTerm00153_eq_value :
    recordGapCenter - 443134 = fullRecordGapValue00153 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00153_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00153 (fullRecordGapValue00153 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00153_not_prime : ¬(recordGapCenter - 443134).Prime := by
  rw [fullRecordGapTerm00153_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00153, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00153_fast_pow_mod_ne_one

def fullRecordGapValue00154 : Nat := fullRecordGapCenterValue - 443098

theorem fullRecordGapTerm00154_eq_value :
    recordGapCenter - 443098 = fullRecordGapValue00154 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00154_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00154 (fullRecordGapValue00154 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00154_not_prime : ¬(recordGapCenter - 443098).Prime := by
  rw [fullRecordGapTerm00154_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00154, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00154_fast_pow_mod_ne_one

def fullRecordGapValue00155 : Nat := fullRecordGapCenterValue - 442984

theorem fullRecordGapTerm00155_eq_value :
    recordGapCenter - 442984 = fullRecordGapValue00155 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00155_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00155 (fullRecordGapValue00155 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00155_not_prime : ¬(recordGapCenter - 442984).Prime := by
  rw [fullRecordGapTerm00155_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00155, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00155_fast_pow_mod_ne_one

def fullRecordGapValue00156 : Nat := fullRecordGapCenterValue - 442978

theorem fullRecordGapTerm00156_eq_value :
    recordGapCenter - 442978 = fullRecordGapValue00156 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00156_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00156 (fullRecordGapValue00156 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00156_not_prime : ¬(recordGapCenter - 442978).Prime := by
  rw [fullRecordGapTerm00156_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00156, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00156_fast_pow_mod_ne_one

def fullRecordGapValue00157 : Nat := fullRecordGapCenterValue - 442938

theorem fullRecordGapTerm00157_eq_value :
    recordGapCenter - 442938 = fullRecordGapValue00157 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00157_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00157 (fullRecordGapValue00157 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00157_not_prime : ¬(recordGapCenter - 442938).Prime := by
  rw [fullRecordGapTerm00157_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00157, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00157_fast_pow_mod_ne_one

def fullRecordGapValue00158 : Nat := fullRecordGapCenterValue - 442924

theorem fullRecordGapTerm00158_eq_value :
    recordGapCenter - 442924 = fullRecordGapValue00158 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00158_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00158 (fullRecordGapValue00158 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00158_not_prime : ¬(recordGapCenter - 442924).Prime := by
  rw [fullRecordGapTerm00158_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00158, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00158_fast_pow_mod_ne_one

def fullRecordGapValue00159 : Nat := fullRecordGapCenterValue - 442914

theorem fullRecordGapTerm00159_eq_value :
    recordGapCenter - 442914 = fullRecordGapValue00159 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00159_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00159 (fullRecordGapValue00159 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00159_not_prime : ¬(recordGapCenter - 442914).Prime := by
  rw [fullRecordGapTerm00159_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00159, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00159_fast_pow_mod_ne_one

def fullRecordGapValue00160 : Nat := fullRecordGapCenterValue - 442588

theorem fullRecordGapTerm00160_eq_value :
    recordGapCenter - 442588 = fullRecordGapValue00160 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00160_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00160 (fullRecordGapValue00160 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00160_not_prime : ¬(recordGapCenter - 442588).Prime := by
  rw [fullRecordGapTerm00160_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00160, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00160_fast_pow_mod_ne_one

def fullRecordGapValue00161 : Nat := fullRecordGapCenterValue - 442564

theorem fullRecordGapTerm00161_eq_value :
    recordGapCenter - 442564 = fullRecordGapValue00161 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00161_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00161 (fullRecordGapValue00161 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00161_not_prime : ¬(recordGapCenter - 442564).Prime := by
  rw [fullRecordGapTerm00161_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00161, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00161_fast_pow_mod_ne_one

def fullRecordGapValue00162 : Nat := fullRecordGapCenterValue - 442542

theorem fullRecordGapTerm00162_eq_value :
    recordGapCenter - 442542 = fullRecordGapValue00162 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00162_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00162 (fullRecordGapValue00162 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00162_not_prime : ¬(recordGapCenter - 442542).Prime := by
  rw [fullRecordGapTerm00162_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00162, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00162_fast_pow_mod_ne_one

def fullRecordGapValue00163 : Nat := fullRecordGapCenterValue - 442438

theorem fullRecordGapTerm00163_eq_value :
    recordGapCenter - 442438 = fullRecordGapValue00163 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00163_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00163 (fullRecordGapValue00163 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00163_not_prime : ¬(recordGapCenter - 442438).Prime := by
  rw [fullRecordGapTerm00163_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00163, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00163_fast_pow_mod_ne_one

def fullRecordGapValue00164 : Nat := fullRecordGapCenterValue - 442368

theorem fullRecordGapTerm00164_eq_value :
    recordGapCenter - 442368 = fullRecordGapValue00164 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00164_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00164 (fullRecordGapValue00164 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00164_not_prime : ¬(recordGapCenter - 442368).Prime := by
  rw [fullRecordGapTerm00164_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00164, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00164_fast_pow_mod_ne_one

def fullRecordGapValue00165 : Nat := fullRecordGapCenterValue - 442362

theorem fullRecordGapTerm00165_eq_value :
    recordGapCenter - 442362 = fullRecordGapValue00165 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00165_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00165 (fullRecordGapValue00165 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00165_not_prime : ¬(recordGapCenter - 442362).Prime := by
  rw [fullRecordGapTerm00165_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00165, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00165_fast_pow_mod_ne_one

def fullRecordGapValue00166 : Nat := fullRecordGapCenterValue - 442210

theorem fullRecordGapTerm00166_eq_value :
    recordGapCenter - 442210 = fullRecordGapValue00166 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00166_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00166 (fullRecordGapValue00166 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00166_not_prime : ¬(recordGapCenter - 442210).Prime := by
  rw [fullRecordGapTerm00166_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00166, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00166_fast_pow_mod_ne_one

def fullRecordGapValue00167 : Nat := fullRecordGapCenterValue - 442132

theorem fullRecordGapTerm00167_eq_value :
    recordGapCenter - 442132 = fullRecordGapValue00167 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00167_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00167 (fullRecordGapValue00167 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00167_not_prime : ¬(recordGapCenter - 442132).Prime := by
  rw [fullRecordGapTerm00167_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00167, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00167_fast_pow_mod_ne_one

def fullRecordGapValue00168 : Nat := fullRecordGapCenterValue - 442074

theorem fullRecordGapTerm00168_eq_value :
    recordGapCenter - 442074 = fullRecordGapValue00168 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00168_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00168 (fullRecordGapValue00168 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00168_not_prime : ¬(recordGapCenter - 442074).Prime := by
  rw [fullRecordGapTerm00168_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00168, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00168_fast_pow_mod_ne_one

def fullRecordGapValue00169 : Nat := fullRecordGapCenterValue - 442042

theorem fullRecordGapTerm00169_eq_value :
    recordGapCenter - 442042 = fullRecordGapValue00169 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00169_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00169 (fullRecordGapValue00169 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00169_not_prime : ¬(recordGapCenter - 442042).Prime := by
  rw [fullRecordGapTerm00169_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00169, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00169_fast_pow_mod_ne_one

def fullRecordGapValue00170 : Nat := fullRecordGapCenterValue - 441814

theorem fullRecordGapTerm00170_eq_value :
    recordGapCenter - 441814 = fullRecordGapValue00170 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00170_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00170 (fullRecordGapValue00170 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00170_not_prime : ¬(recordGapCenter - 441814).Prime := by
  rw [fullRecordGapTerm00170_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00170, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00170_fast_pow_mod_ne_one

def fullRecordGapValue00171 : Nat := fullRecordGapCenterValue - 441802

theorem fullRecordGapTerm00171_eq_value :
    recordGapCenter - 441802 = fullRecordGapValue00171 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00171_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00171 (fullRecordGapValue00171 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00171_not_prime : ¬(recordGapCenter - 441802).Prime := by
  rw [fullRecordGapTerm00171_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00171, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00171_fast_pow_mod_ne_one

def fullRecordGapValue00172 : Nat := fullRecordGapCenterValue - 441682

theorem fullRecordGapTerm00172_eq_value :
    recordGapCenter - 441682 = fullRecordGapValue00172 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00172_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00172 (fullRecordGapValue00172 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00172_not_prime : ¬(recordGapCenter - 441682).Prime := by
  rw [fullRecordGapTerm00172_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00172, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00172_fast_pow_mod_ne_one

def fullRecordGapValue00173 : Nat := fullRecordGapCenterValue - 441622

theorem fullRecordGapTerm00173_eq_value :
    recordGapCenter - 441622 = fullRecordGapValue00173 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00173_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00173 (fullRecordGapValue00173 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00173_not_prime : ¬(recordGapCenter - 441622).Prime := by
  rw [fullRecordGapTerm00173_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00173, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00173_fast_pow_mod_ne_one

def fullRecordGapValue00174 : Nat := fullRecordGapCenterValue - 441318

theorem fullRecordGapTerm00174_eq_value :
    recordGapCenter - 441318 = fullRecordGapValue00174 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00174_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00174 (fullRecordGapValue00174 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00174_not_prime : ¬(recordGapCenter - 441318).Prime := by
  rw [fullRecordGapTerm00174_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00174, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00174_fast_pow_mod_ne_one

def fullRecordGapValue00175 : Nat := fullRecordGapCenterValue - 441310

theorem fullRecordGapTerm00175_eq_value :
    recordGapCenter - 441310 = fullRecordGapValue00175 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00175_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00175 (fullRecordGapValue00175 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00175_not_prime : ¬(recordGapCenter - 441310).Prime := by
  rw [fullRecordGapTerm00175_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00175, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00175_fast_pow_mod_ne_one

def fullRecordGapValue00176 : Nat := fullRecordGapCenterValue - 441304

theorem fullRecordGapTerm00176_eq_value :
    recordGapCenter - 441304 = fullRecordGapValue00176 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00176_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00176 (fullRecordGapValue00176 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00176_not_prime : ¬(recordGapCenter - 441304).Prime := by
  rw [fullRecordGapTerm00176_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00176, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00176_fast_pow_mod_ne_one

def fullRecordGapValue00177 : Nat := fullRecordGapCenterValue - 441292

theorem fullRecordGapTerm00177_eq_value :
    recordGapCenter - 441292 = fullRecordGapValue00177 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00177_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00177 (fullRecordGapValue00177 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00177_not_prime : ¬(recordGapCenter - 441292).Prime := by
  rw [fullRecordGapTerm00177_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00177, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00177_fast_pow_mod_ne_one

def fullRecordGapValue00178 : Nat := fullRecordGapCenterValue - 441178

theorem fullRecordGapTerm00178_eq_value :
    recordGapCenter - 441178 = fullRecordGapValue00178 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00178_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00178 (fullRecordGapValue00178 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00178_not_prime : ¬(recordGapCenter - 441178).Prime := by
  rw [fullRecordGapTerm00178_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00178, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00178_fast_pow_mod_ne_one

def fullRecordGapValue00179 : Nat := fullRecordGapCenterValue - 441138

theorem fullRecordGapTerm00179_eq_value :
    recordGapCenter - 441138 = fullRecordGapValue00179 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00179_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00179 (fullRecordGapValue00179 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00179_not_prime : ¬(recordGapCenter - 441138).Prime := by
  rw [fullRecordGapTerm00179_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00179, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00179_fast_pow_mod_ne_one

def fullRecordGapValue00180 : Nat := fullRecordGapCenterValue - 441010

theorem fullRecordGapTerm00180_eq_value :
    recordGapCenter - 441010 = fullRecordGapValue00180 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00180_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00180 (fullRecordGapValue00180 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00180_not_prime : ¬(recordGapCenter - 441010).Prime := by
  rw [fullRecordGapTerm00180_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00180, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00180_fast_pow_mod_ne_one

def fullRecordGapValue00181 : Nat := fullRecordGapCenterValue - 440872

theorem fullRecordGapTerm00181_eq_value :
    recordGapCenter - 440872 = fullRecordGapValue00181 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00181_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00181 (fullRecordGapValue00181 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00181_not_prime : ¬(recordGapCenter - 440872).Prime := by
  rw [fullRecordGapTerm00181_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00181, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00181_fast_pow_mod_ne_one

def fullRecordGapValue00182 : Nat := fullRecordGapCenterValue - 440824

theorem fullRecordGapTerm00182_eq_value :
    recordGapCenter - 440824 = fullRecordGapValue00182 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00182_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00182 (fullRecordGapValue00182 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00182_not_prime : ¬(recordGapCenter - 440824).Prime := by
  rw [fullRecordGapTerm00182_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00182, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00182_fast_pow_mod_ne_one

def fullRecordGapValue00183 : Nat := fullRecordGapCenterValue - 440782

theorem fullRecordGapTerm00183_eq_value :
    recordGapCenter - 440782 = fullRecordGapValue00183 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00183_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00183 (fullRecordGapValue00183 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00183_not_prime : ¬(recordGapCenter - 440782).Prime := by
  rw [fullRecordGapTerm00183_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00183, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00183_fast_pow_mod_ne_one

def fullRecordGapValue00184 : Nat := fullRecordGapCenterValue - 440718

theorem fullRecordGapTerm00184_eq_value :
    recordGapCenter - 440718 = fullRecordGapValue00184 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00184_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00184 (fullRecordGapValue00184 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00184_not_prime : ¬(recordGapCenter - 440718).Prime := by
  rw [fullRecordGapTerm00184_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00184, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00184_fast_pow_mod_ne_one

def fullRecordGapValue00185 : Nat := fullRecordGapCenterValue - 440614

theorem fullRecordGapTerm00185_eq_value :
    recordGapCenter - 440614 = fullRecordGapValue00185 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00185_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00185 (fullRecordGapValue00185 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00185_not_prime : ¬(recordGapCenter - 440614).Prime := by
  rw [fullRecordGapTerm00185_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00185, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00185_fast_pow_mod_ne_one

def fullRecordGapValue00186 : Nat := fullRecordGapCenterValue - 440584

theorem fullRecordGapTerm00186_eq_value :
    recordGapCenter - 440584 = fullRecordGapValue00186 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00186_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00186 (fullRecordGapValue00186 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00186_not_prime : ¬(recordGapCenter - 440584).Prime := by
  rw [fullRecordGapTerm00186_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00186, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00186_fast_pow_mod_ne_one

def fullRecordGapValue00187 : Nat := fullRecordGapCenterValue - 440502

theorem fullRecordGapTerm00187_eq_value :
    recordGapCenter - 440502 = fullRecordGapValue00187 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00187_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00187 (fullRecordGapValue00187 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00187_not_prime : ¬(recordGapCenter - 440502).Prime := by
  rw [fullRecordGapTerm00187_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00187, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00187_fast_pow_mod_ne_one

def fullRecordGapValue00188 : Nat := fullRecordGapCenterValue - 440338

theorem fullRecordGapTerm00188_eq_value :
    recordGapCenter - 440338 = fullRecordGapValue00188 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00188_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00188 (fullRecordGapValue00188 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00188_not_prime : ¬(recordGapCenter - 440338).Prime := by
  rw [fullRecordGapTerm00188_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00188, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00188_fast_pow_mod_ne_one

def fullRecordGapValue00189 : Nat := fullRecordGapCenterValue - 440332

theorem fullRecordGapTerm00189_eq_value :
    recordGapCenter - 440332 = fullRecordGapValue00189 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00189_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00189 (fullRecordGapValue00189 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00189_not_prime : ¬(recordGapCenter - 440332).Prime := by
  rw [fullRecordGapTerm00189_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00189, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00189_fast_pow_mod_ne_one

def fullRecordGapValue00190 : Nat := fullRecordGapCenterValue - 440178

theorem fullRecordGapTerm00190_eq_value :
    recordGapCenter - 440178 = fullRecordGapValue00190 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00190_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00190 (fullRecordGapValue00190 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00190_not_prime : ¬(recordGapCenter - 440178).Prime := by
  rw [fullRecordGapTerm00190_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00190, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00190_fast_pow_mod_ne_one

def fullRecordGapValue00191 : Nat := fullRecordGapCenterValue - 440170

theorem fullRecordGapTerm00191_eq_value :
    recordGapCenter - 440170 = fullRecordGapValue00191 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00191_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00191 (fullRecordGapValue00191 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00191_not_prime : ¬(recordGapCenter - 440170).Prime := by
  rw [fullRecordGapTerm00191_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00191, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00191_fast_pow_mod_ne_one

def fullRecordGapValue00192 : Nat := fullRecordGapCenterValue - 440038

theorem fullRecordGapTerm00192_eq_value :
    recordGapCenter - 440038 = fullRecordGapValue00192 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00192_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00192 (fullRecordGapValue00192 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00192_not_prime : ¬(recordGapCenter - 440038).Prime := by
  rw [fullRecordGapTerm00192_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00192, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00192_fast_pow_mod_ne_one

def fullRecordGapValue00193 : Nat := fullRecordGapCenterValue - 439870

theorem fullRecordGapTerm00193_eq_value :
    recordGapCenter - 439870 = fullRecordGapValue00193 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00193_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00193 (fullRecordGapValue00193 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00193_not_prime : ¬(recordGapCenter - 439870).Prime := by
  rw [fullRecordGapTerm00193_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00193, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00193_fast_pow_mod_ne_one

def fullRecordGapValue00194 : Nat := fullRecordGapCenterValue - 439864

theorem fullRecordGapTerm00194_eq_value :
    recordGapCenter - 439864 = fullRecordGapValue00194 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00194_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00194 (fullRecordGapValue00194 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00194_not_prime : ¬(recordGapCenter - 439864).Prime := by
  rw [fullRecordGapTerm00194_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00194, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00194_fast_pow_mod_ne_one

def fullRecordGapValue00195 : Nat := fullRecordGapCenterValue - 439834

theorem fullRecordGapTerm00195_eq_value :
    recordGapCenter - 439834 = fullRecordGapValue00195 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00195_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00195 (fullRecordGapValue00195 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00195_not_prime : ¬(recordGapCenter - 439834).Prime := by
  rw [fullRecordGapTerm00195_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00195, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00195_fast_pow_mod_ne_one

def fullRecordGapValue00196 : Nat := fullRecordGapCenterValue - 439690

theorem fullRecordGapTerm00196_eq_value :
    recordGapCenter - 439690 = fullRecordGapValue00196 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00196_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00196 (fullRecordGapValue00196 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00196_not_prime : ¬(recordGapCenter - 439690).Prime := by
  rw [fullRecordGapTerm00196_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00196, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00196_fast_pow_mod_ne_one

def fullRecordGapValue00197 : Nat := fullRecordGapCenterValue - 439618

theorem fullRecordGapTerm00197_eq_value :
    recordGapCenter - 439618 = fullRecordGapValue00197 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00197_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00197 (fullRecordGapValue00197 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00197_not_prime : ¬(recordGapCenter - 439618).Prime := by
  rw [fullRecordGapTerm00197_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00197, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00197_fast_pow_mod_ne_one

def fullRecordGapValue00198 : Nat := fullRecordGapCenterValue - 439554

theorem fullRecordGapTerm00198_eq_value :
    recordGapCenter - 439554 = fullRecordGapValue00198 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00198_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00198 (fullRecordGapValue00198 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00198_not_prime : ¬(recordGapCenter - 439554).Prime := by
  rw [fullRecordGapTerm00198_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00198, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00198_fast_pow_mod_ne_one

def fullRecordGapValue00199 : Nat := fullRecordGapCenterValue - 439522

theorem fullRecordGapTerm00199_eq_value :
    recordGapCenter - 439522 = fullRecordGapValue00199 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00199_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00199 (fullRecordGapValue00199 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00199_not_prime : ¬(recordGapCenter - 439522).Prime := by
  rw [fullRecordGapTerm00199_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00199, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00199_fast_pow_mod_ne_one

def fullRecordGapValue00200 : Nat := fullRecordGapCenterValue - 439422

theorem fullRecordGapTerm00200_eq_value :
    recordGapCenter - 439422 = fullRecordGapValue00200 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00200_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00200 (fullRecordGapValue00200 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00200_not_prime : ¬(recordGapCenter - 439422).Prime := by
  rw [fullRecordGapTerm00200_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00200, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00200_fast_pow_mod_ne_one

def fullRecordGapValue00201 : Nat := fullRecordGapCenterValue - 439378

theorem fullRecordGapTerm00201_eq_value :
    recordGapCenter - 439378 = fullRecordGapValue00201 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00201_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00201 (fullRecordGapValue00201 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00201_not_prime : ¬(recordGapCenter - 439378).Prime := by
  rw [fullRecordGapTerm00201_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00201, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00201_fast_pow_mod_ne_one

def fullRecordGapValue00202 : Nat := fullRecordGapCenterValue - 439372

theorem fullRecordGapTerm00202_eq_value :
    recordGapCenter - 439372 = fullRecordGapValue00202 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00202_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00202 (fullRecordGapValue00202 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00202_not_prime : ¬(recordGapCenter - 439372).Prime := by
  rw [fullRecordGapTerm00202_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00202, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00202_fast_pow_mod_ne_one

def fullRecordGapValue00203 : Nat := fullRecordGapCenterValue - 439354

theorem fullRecordGapTerm00203_eq_value :
    recordGapCenter - 439354 = fullRecordGapValue00203 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00203_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00203 (fullRecordGapValue00203 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00203_not_prime : ¬(recordGapCenter - 439354).Prime := by
  rw [fullRecordGapTerm00203_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00203, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00203_fast_pow_mod_ne_one

def fullRecordGapValue00204 : Nat := fullRecordGapCenterValue - 439324

theorem fullRecordGapTerm00204_eq_value :
    recordGapCenter - 439324 = fullRecordGapValue00204 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00204_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00204 (fullRecordGapValue00204 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00204_not_prime : ¬(recordGapCenter - 439324).Prime := by
  rw [fullRecordGapTerm00204_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00204, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00204_fast_pow_mod_ne_one

def fullRecordGapValue00205 : Nat := fullRecordGapCenterValue - 438868

theorem fullRecordGapTerm00205_eq_value :
    recordGapCenter - 438868 = fullRecordGapValue00205 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00205_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00205 (fullRecordGapValue00205 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00205_not_prime : ¬(recordGapCenter - 438868).Prime := by
  rw [fullRecordGapTerm00205_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00205, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00205_fast_pow_mod_ne_one

def fullRecordGapValue00206 : Nat := fullRecordGapCenterValue - 438808

theorem fullRecordGapTerm00206_eq_value :
    recordGapCenter - 438808 = fullRecordGapValue00206 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00206_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00206 (fullRecordGapValue00206 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00206_not_prime : ¬(recordGapCenter - 438808).Prime := by
  rw [fullRecordGapTerm00206_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00206, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00206_fast_pow_mod_ne_one

def fullRecordGapValue00207 : Nat := fullRecordGapCenterValue - 438778

theorem fullRecordGapTerm00207_eq_value :
    recordGapCenter - 438778 = fullRecordGapValue00207 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00207_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00207 (fullRecordGapValue00207 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00207_not_prime : ¬(recordGapCenter - 438778).Prime := by
  rw [fullRecordGapTerm00207_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00207, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00207_fast_pow_mod_ne_one

def fullRecordGapValue00208 : Nat := fullRecordGapCenterValue - 438762

theorem fullRecordGapTerm00208_eq_value :
    recordGapCenter - 438762 = fullRecordGapValue00208 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00208_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00208 (fullRecordGapValue00208 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00208_not_prime : ¬(recordGapCenter - 438762).Prime := by
  rw [fullRecordGapTerm00208_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00208, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00208_fast_pow_mod_ne_one

def fullRecordGapValue00209 : Nat := fullRecordGapCenterValue - 438562

theorem fullRecordGapTerm00209_eq_value :
    recordGapCenter - 438562 = fullRecordGapValue00209 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00209_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00209 (fullRecordGapValue00209 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00209_not_prime : ¬(recordGapCenter - 438562).Prime := by
  rw [fullRecordGapTerm00209_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00209, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00209_fast_pow_mod_ne_one

def fullRecordGapValue00210 : Nat := fullRecordGapCenterValue - 438388

theorem fullRecordGapTerm00210_eq_value :
    recordGapCenter - 438388 = fullRecordGapValue00210 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00210_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00210 (fullRecordGapValue00210 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00210_not_prime : ¬(recordGapCenter - 438388).Prime := by
  rw [fullRecordGapTerm00210_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00210, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00210_fast_pow_mod_ne_one

def fullRecordGapValue00211 : Nat := fullRecordGapCenterValue - 438378

theorem fullRecordGapTerm00211_eq_value :
    recordGapCenter - 438378 = fullRecordGapValue00211 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00211_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00211 (fullRecordGapValue00211 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00211_not_prime : ¬(recordGapCenter - 438378).Prime := by
  rw [fullRecordGapTerm00211_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00211, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00211_fast_pow_mod_ne_one

def fullRecordGapValue00212 : Nat := fullRecordGapCenterValue - 438258

theorem fullRecordGapTerm00212_eq_value :
    recordGapCenter - 438258 = fullRecordGapValue00212 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00212_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00212 (fullRecordGapValue00212 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00212_not_prime : ¬(recordGapCenter - 438258).Prime := by
  rw [fullRecordGapTerm00212_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00212, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00212_fast_pow_mod_ne_one

def fullRecordGapValue00213 : Nat := fullRecordGapCenterValue - 438234

theorem fullRecordGapTerm00213_eq_value :
    recordGapCenter - 438234 = fullRecordGapValue00213 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00213_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00213 (fullRecordGapValue00213 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00213_not_prime : ¬(recordGapCenter - 438234).Prime := by
  rw [fullRecordGapTerm00213_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00213, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00213_fast_pow_mod_ne_one

def fullRecordGapValue00214 : Nat := fullRecordGapCenterValue - 438184

theorem fullRecordGapTerm00214_eq_value :
    recordGapCenter - 438184 = fullRecordGapValue00214 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00214_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00214 (fullRecordGapValue00214 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00214_not_prime : ¬(recordGapCenter - 438184).Prime := by
  rw [fullRecordGapTerm00214_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00214, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00214_fast_pow_mod_ne_one

def fullRecordGapValue00215 : Nat := fullRecordGapCenterValue - 438114

theorem fullRecordGapTerm00215_eq_value :
    recordGapCenter - 438114 = fullRecordGapValue00215 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00215_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00215 (fullRecordGapValue00215 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00215_not_prime : ¬(recordGapCenter - 438114).Prime := by
  rw [fullRecordGapTerm00215_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00215, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00215_fast_pow_mod_ne_one

def fullRecordGapValue00216 : Nat := fullRecordGapCenterValue - 438078

theorem fullRecordGapTerm00216_eq_value :
    recordGapCenter - 438078 = fullRecordGapValue00216 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00216_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00216 (fullRecordGapValue00216 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00216_not_prime : ¬(recordGapCenter - 438078).Prime := by
  rw [fullRecordGapTerm00216_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00216, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00216_fast_pow_mod_ne_one

def fullRecordGapValue00217 : Nat := fullRecordGapCenterValue - 437982

theorem fullRecordGapTerm00217_eq_value :
    recordGapCenter - 437982 = fullRecordGapValue00217 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00217_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00217 (fullRecordGapValue00217 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00217_not_prime : ¬(recordGapCenter - 437982).Prime := by
  rw [fullRecordGapTerm00217_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00217, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00217_fast_pow_mod_ne_one

def fullRecordGapValue00218 : Nat := fullRecordGapCenterValue - 437812

theorem fullRecordGapTerm00218_eq_value :
    recordGapCenter - 437812 = fullRecordGapValue00218 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00218_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00218 (fullRecordGapValue00218 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00218_not_prime : ¬(recordGapCenter - 437812).Prime := by
  rw [fullRecordGapTerm00218_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00218, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00218_fast_pow_mod_ne_one

def fullRecordGapValue00219 : Nat := fullRecordGapCenterValue - 437622

theorem fullRecordGapTerm00219_eq_value :
    recordGapCenter - 437622 = fullRecordGapValue00219 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00219_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00219 (fullRecordGapValue00219 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00219_not_prime : ¬(recordGapCenter - 437622).Prime := by
  rw [fullRecordGapTerm00219_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00219, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00219_fast_pow_mod_ne_one

def fullRecordGapValue00220 : Nat := fullRecordGapCenterValue - 437590

theorem fullRecordGapTerm00220_eq_value :
    recordGapCenter - 437590 = fullRecordGapValue00220 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00220_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00220 (fullRecordGapValue00220 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00220_not_prime : ¬(recordGapCenter - 437590).Prime := by
  rw [fullRecordGapTerm00220_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00220, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00220_fast_pow_mod_ne_one

def fullRecordGapValue00221 : Nat := fullRecordGapCenterValue - 437538

theorem fullRecordGapTerm00221_eq_value :
    recordGapCenter - 437538 = fullRecordGapValue00221 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00221_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00221 (fullRecordGapValue00221 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00221_not_prime : ¬(recordGapCenter - 437538).Prime := by
  rw [fullRecordGapTerm00221_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00221, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00221_fast_pow_mod_ne_one

def fullRecordGapValue00222 : Nat := fullRecordGapCenterValue - 437530

theorem fullRecordGapTerm00222_eq_value :
    recordGapCenter - 437530 = fullRecordGapValue00222 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00222_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00222 (fullRecordGapValue00222 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00222_not_prime : ¬(recordGapCenter - 437530).Prime := by
  rw [fullRecordGapTerm00222_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00222, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00222_fast_pow_mod_ne_one

def fullRecordGapValue00223 : Nat := fullRecordGapCenterValue - 437434

theorem fullRecordGapTerm00223_eq_value :
    recordGapCenter - 437434 = fullRecordGapValue00223 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00223_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00223 (fullRecordGapValue00223 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00223_not_prime : ¬(recordGapCenter - 437434).Prime := by
  rw [fullRecordGapTerm00223_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00223, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00223_fast_pow_mod_ne_one

def fullRecordGapValue00224 : Nat := fullRecordGapCenterValue - 437422

theorem fullRecordGapTerm00224_eq_value :
    recordGapCenter - 437422 = fullRecordGapValue00224 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00224_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00224 (fullRecordGapValue00224 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00224_not_prime : ¬(recordGapCenter - 437422).Prime := by
  rw [fullRecordGapTerm00224_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00224, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00224_fast_pow_mod_ne_one

def fullRecordGapValue00225 : Nat := fullRecordGapCenterValue - 437400

theorem fullRecordGapTerm00225_eq_value :
    recordGapCenter - 437400 = fullRecordGapValue00225 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00225_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00225 (fullRecordGapValue00225 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00225_not_prime : ¬(recordGapCenter - 437400).Prime := by
  rw [fullRecordGapTerm00225_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00225, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00225_fast_pow_mod_ne_one

def fullRecordGapValue00226 : Nat := fullRecordGapCenterValue - 437358

theorem fullRecordGapTerm00226_eq_value :
    recordGapCenter - 437358 = fullRecordGapValue00226 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00226_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00226 (fullRecordGapValue00226 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00226_not_prime : ¬(recordGapCenter - 437358).Prime := by
  rw [fullRecordGapTerm00226_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00226, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00226_fast_pow_mod_ne_one

def fullRecordGapValue00227 : Nat := fullRecordGapCenterValue - 437334

theorem fullRecordGapTerm00227_eq_value :
    recordGapCenter - 437334 = fullRecordGapValue00227 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00227_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00227 (fullRecordGapValue00227 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00227_not_prime : ¬(recordGapCenter - 437334).Prime := by
  rw [fullRecordGapTerm00227_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00227, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00227_fast_pow_mod_ne_one

def fullRecordGapValue00228 : Nat := fullRecordGapCenterValue - 437314

theorem fullRecordGapTerm00228_eq_value :
    recordGapCenter - 437314 = fullRecordGapValue00228 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00228_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00228 (fullRecordGapValue00228 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00228_not_prime : ¬(recordGapCenter - 437314).Prime := by
  rw [fullRecordGapTerm00228_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00228, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00228_fast_pow_mod_ne_one

def fullRecordGapValue00229 : Nat := fullRecordGapCenterValue - 437182

theorem fullRecordGapTerm00229_eq_value :
    recordGapCenter - 437182 = fullRecordGapValue00229 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00229_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00229 (fullRecordGapValue00229 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00229_not_prime : ¬(recordGapCenter - 437182).Prime := by
  rw [fullRecordGapTerm00229_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00229, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00229_fast_pow_mod_ne_one

def fullRecordGapValue00230 : Nat := fullRecordGapCenterValue - 437170

theorem fullRecordGapTerm00230_eq_value :
    recordGapCenter - 437170 = fullRecordGapValue00230 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00230_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00230 (fullRecordGapValue00230 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00230_not_prime : ¬(recordGapCenter - 437170).Prime := by
  rw [fullRecordGapTerm00230_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00230, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00230_fast_pow_mod_ne_one

def fullRecordGapValue00231 : Nat := fullRecordGapCenterValue - 437098

theorem fullRecordGapTerm00231_eq_value :
    recordGapCenter - 437098 = fullRecordGapValue00231 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00231_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00231 (fullRecordGapValue00231 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00231_not_prime : ¬(recordGapCenter - 437098).Prime := by
  rw [fullRecordGapTerm00231_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00231, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00231_fast_pow_mod_ne_one

def fullRecordGapValue00232 : Nat := fullRecordGapCenterValue - 437068

theorem fullRecordGapTerm00232_eq_value :
    recordGapCenter - 437068 = fullRecordGapValue00232 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00232_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00232 (fullRecordGapValue00232 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00232_not_prime : ¬(recordGapCenter - 437068).Prime := by
  rw [fullRecordGapTerm00232_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00232, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00232_fast_pow_mod_ne_one

def fullRecordGapValue00233 : Nat := fullRecordGapCenterValue - 436762

theorem fullRecordGapTerm00233_eq_value :
    recordGapCenter - 436762 = fullRecordGapValue00233 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00233_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00233 (fullRecordGapValue00233 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00233_not_prime : ¬(recordGapCenter - 436762).Prime := by
  rw [fullRecordGapTerm00233_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00233, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00233_fast_pow_mod_ne_one

def fullRecordGapValue00234 : Nat := fullRecordGapCenterValue - 436684

theorem fullRecordGapTerm00234_eq_value :
    recordGapCenter - 436684 = fullRecordGapValue00234 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00234_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00234 (fullRecordGapValue00234 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00234_not_prime : ¬(recordGapCenter - 436684).Prime := by
  rw [fullRecordGapTerm00234_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00234, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00234_fast_pow_mod_ne_one

def fullRecordGapValue00235 : Nat := fullRecordGapCenterValue - 436578

theorem fullRecordGapTerm00235_eq_value :
    recordGapCenter - 436578 = fullRecordGapValue00235 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00235_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00235 (fullRecordGapValue00235 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00235_not_prime : ¬(recordGapCenter - 436578).Prime := by
  rw [fullRecordGapTerm00235_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00235, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00235_fast_pow_mod_ne_one

def fullRecordGapValue00236 : Nat := fullRecordGapCenterValue - 436510

theorem fullRecordGapTerm00236_eq_value :
    recordGapCenter - 436510 = fullRecordGapValue00236 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00236_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00236 (fullRecordGapValue00236 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00236_not_prime : ¬(recordGapCenter - 436510).Prime := by
  rw [fullRecordGapTerm00236_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00236, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00236_fast_pow_mod_ne_one

def fullRecordGapValue00237 : Nat := fullRecordGapCenterValue - 436504

theorem fullRecordGapTerm00237_eq_value :
    recordGapCenter - 436504 = fullRecordGapValue00237 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00237_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00237 (fullRecordGapValue00237 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00237_not_prime : ¬(recordGapCenter - 436504).Prime := by
  rw [fullRecordGapTerm00237_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00237, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00237_fast_pow_mod_ne_one

def fullRecordGapValue00238 : Nat := fullRecordGapCenterValue - 436498

theorem fullRecordGapTerm00238_eq_value :
    recordGapCenter - 436498 = fullRecordGapValue00238 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00238_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00238 (fullRecordGapValue00238 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00238_not_prime : ¬(recordGapCenter - 436498).Prime := by
  rw [fullRecordGapTerm00238_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00238, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00238_fast_pow_mod_ne_one

def fullRecordGapValue00239 : Nat := fullRecordGapCenterValue - 436362

theorem fullRecordGapTerm00239_eq_value :
    recordGapCenter - 436362 = fullRecordGapValue00239 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00239_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00239 (fullRecordGapValue00239 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00239_not_prime : ¬(recordGapCenter - 436362).Prime := by
  rw [fullRecordGapTerm00239_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00239, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00239_fast_pow_mod_ne_one

def fullRecordGapValue00240 : Nat := fullRecordGapCenterValue - 436312

theorem fullRecordGapTerm00240_eq_value :
    recordGapCenter - 436312 = fullRecordGapValue00240 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00240_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00240 (fullRecordGapValue00240 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00240_not_prime : ¬(recordGapCenter - 436312).Prime := by
  rw [fullRecordGapTerm00240_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00240, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00240_fast_pow_mod_ne_one

def fullRecordGapValue00241 : Nat := fullRecordGapCenterValue - 436270

theorem fullRecordGapTerm00241_eq_value :
    recordGapCenter - 436270 = fullRecordGapValue00241 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00241_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00241 (fullRecordGapValue00241 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00241_not_prime : ¬(recordGapCenter - 436270).Prime := by
  rw [fullRecordGapTerm00241_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00241, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00241_fast_pow_mod_ne_one

def fullRecordGapValue00242 : Nat := fullRecordGapCenterValue - 436252

theorem fullRecordGapTerm00242_eq_value :
    recordGapCenter - 436252 = fullRecordGapValue00242 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00242_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00242 (fullRecordGapValue00242 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00242_not_prime : ¬(recordGapCenter - 436252).Prime := by
  rw [fullRecordGapTerm00242_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00242, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00242_fast_pow_mod_ne_one

def fullRecordGapValue00243 : Nat := fullRecordGapCenterValue - 436138

theorem fullRecordGapTerm00243_eq_value :
    recordGapCenter - 436138 = fullRecordGapValue00243 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00243_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00243 (fullRecordGapValue00243 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00243_not_prime : ¬(recordGapCenter - 436138).Prime := by
  rw [fullRecordGapTerm00243_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00243, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00243_fast_pow_mod_ne_one

def fullRecordGapValue00244 : Nat := fullRecordGapCenterValue - 436134

theorem fullRecordGapTerm00244_eq_value :
    recordGapCenter - 436134 = fullRecordGapValue00244 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00244_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00244 (fullRecordGapValue00244 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00244_not_prime : ¬(recordGapCenter - 436134).Prime := by
  rw [fullRecordGapTerm00244_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00244, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00244_fast_pow_mod_ne_one

def fullRecordGapValue00245 : Nat := fullRecordGapCenterValue - 436074

theorem fullRecordGapTerm00245_eq_value :
    recordGapCenter - 436074 = fullRecordGapValue00245 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00245_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00245 (fullRecordGapValue00245 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00245_not_prime : ¬(recordGapCenter - 436074).Prime := by
  rw [fullRecordGapTerm00245_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00245, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00245_fast_pow_mod_ne_one

def fullRecordGapValue00246 : Nat := fullRecordGapCenterValue - 436042

theorem fullRecordGapTerm00246_eq_value :
    recordGapCenter - 436042 = fullRecordGapValue00246 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00246_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00246 (fullRecordGapValue00246 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00246_not_prime : ¬(recordGapCenter - 436042).Prime := by
  rw [fullRecordGapTerm00246_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00246, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00246_fast_pow_mod_ne_one

def fullRecordGapValue00247 : Nat := fullRecordGapCenterValue - 435970

theorem fullRecordGapTerm00247_eq_value :
    recordGapCenter - 435970 = fullRecordGapValue00247 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00247_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00247 (fullRecordGapValue00247 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00247_not_prime : ¬(recordGapCenter - 435970).Prime := by
  rw [fullRecordGapTerm00247_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00247, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00247_fast_pow_mod_ne_one

def fullRecordGapValue00248 : Nat := fullRecordGapCenterValue - 435964

theorem fullRecordGapTerm00248_eq_value :
    recordGapCenter - 435964 = fullRecordGapValue00248 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00248_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00248 (fullRecordGapValue00248 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00248_not_prime : ¬(recordGapCenter - 435964).Prime := by
  rw [fullRecordGapTerm00248_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00248, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00248_fast_pow_mod_ne_one

def fullRecordGapValue00249 : Nat := fullRecordGapCenterValue - 435958

theorem fullRecordGapTerm00249_eq_value :
    recordGapCenter - 435958 = fullRecordGapValue00249 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00249_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00249 (fullRecordGapValue00249 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00249_not_prime : ¬(recordGapCenter - 435958).Prime := by
  rw [fullRecordGapTerm00249_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00249, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00249_fast_pow_mod_ne_one

def fullRecordGapValue00250 : Nat := fullRecordGapCenterValue - 435894

theorem fullRecordGapTerm00250_eq_value :
    recordGapCenter - 435894 = fullRecordGapValue00250 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00250_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00250 (fullRecordGapValue00250 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00250_not_prime : ¬(recordGapCenter - 435894).Prime := by
  rw [fullRecordGapTerm00250_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00250, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00250_fast_pow_mod_ne_one

def fullRecordGapValue00251 : Nat := fullRecordGapCenterValue - 435882

theorem fullRecordGapTerm00251_eq_value :
    recordGapCenter - 435882 = fullRecordGapValue00251 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00251_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00251 (fullRecordGapValue00251 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00251_not_prime : ¬(recordGapCenter - 435882).Prime := by
  rw [fullRecordGapTerm00251_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00251, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00251_fast_pow_mod_ne_one

def fullRecordGapValue00252 : Nat := fullRecordGapCenterValue - 435874

theorem fullRecordGapTerm00252_eq_value :
    recordGapCenter - 435874 = fullRecordGapValue00252 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00252_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00252 (fullRecordGapValue00252 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00252_not_prime : ¬(recordGapCenter - 435874).Prime := by
  rw [fullRecordGapTerm00252_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00252, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00252_fast_pow_mod_ne_one

def fullRecordGapValue00253 : Nat := fullRecordGapCenterValue - 435858

theorem fullRecordGapTerm00253_eq_value :
    recordGapCenter - 435858 = fullRecordGapValue00253 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00253_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00253 (fullRecordGapValue00253 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00253_not_prime : ¬(recordGapCenter - 435858).Prime := by
  rw [fullRecordGapTerm00253_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00253, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00253_fast_pow_mod_ne_one

def fullRecordGapValue00254 : Nat := fullRecordGapCenterValue - 435844

theorem fullRecordGapTerm00254_eq_value :
    recordGapCenter - 435844 = fullRecordGapValue00254 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00254_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00254 (fullRecordGapValue00254 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00254_not_prime : ¬(recordGapCenter - 435844).Prime := by
  rw [fullRecordGapTerm00254_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00254, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00254_fast_pow_mod_ne_one

def fullRecordGapValue00255 : Nat := fullRecordGapCenterValue - 435738

theorem fullRecordGapTerm00255_eq_value :
    recordGapCenter - 435738 = fullRecordGapValue00255 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00255_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00255 (fullRecordGapValue00255 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00255_not_prime : ¬(recordGapCenter - 435738).Prime := by
  rw [fullRecordGapTerm00255_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00255, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00255_fast_pow_mod_ne_one

def fullRecordGapValue00256 : Nat := fullRecordGapCenterValue - 435718

theorem fullRecordGapTerm00256_eq_value :
    recordGapCenter - 435718 = fullRecordGapValue00256 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral00256_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue00256 (fullRecordGapValue00256 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00256_not_prime : ¬(recordGapCenter - 435718).Prime := by
  rw [fullRecordGapTerm00256_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue00256, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral00256_fast_pow_mod_ne_one

end PrimeFactorUnimodality
