import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00002_values : List Nat :=
  [fullRecordGapCenterValue - 450292,
    fullRecordGapCenterValue - 450174,
    fullRecordGapCenterValue - 450154,
    fullRecordGapCenterValue - 450130,
    fullRecordGapCenterValue - 450078,
    fullRecordGapCenterValue - 450004,
    fullRecordGapCenterValue - 449782,
    fullRecordGapCenterValue - 449710,
    fullRecordGapCenterValue - 449518,
    fullRecordGapCenterValue - 449368,
    fullRecordGapCenterValue - 449188,
    fullRecordGapCenterValue - 448984,
    fullRecordGapCenterValue - 448962,
    fullRecordGapCenterValue - 448852,
    fullRecordGapCenterValue - 448828,
    fullRecordGapCenterValue - 448648,
    fullRecordGapCenterValue - 448534,
    fullRecordGapCenterValue - 448444,
    fullRecordGapCenterValue - 448348,
    fullRecordGapCenterValue - 448278,
    fullRecordGapCenterValue - 448258,
    fullRecordGapCenterValue - 448138,
    fullRecordGapCenterValue - 448072,
    fullRecordGapCenterValue - 448054,
    fullRecordGapCenterValue - 447970,
    fullRecordGapCenterValue - 447838,
    fullRecordGapCenterValue - 447730,
    fullRecordGapCenterValue - 447652,
    fullRecordGapCenterValue - 447592,
    fullRecordGapCenterValue - 447514,
    fullRecordGapCenterValue - 447394,
    fullRecordGapCenterValue - 447334,
    fullRecordGapCenterValue - 447208,
    fullRecordGapCenterValue - 447058,
    fullRecordGapCenterValue - 447054,
    fullRecordGapCenterValue - 446968,
    fullRecordGapCenterValue - 446962,
    fullRecordGapCenterValue - 446938,
    fullRecordGapCenterValue - 446932,
    fullRecordGapCenterValue - 446878,
    fullRecordGapCenterValue - 446722,
    fullRecordGapCenterValue - 446718,
    fullRecordGapCenterValue - 446694,
    fullRecordGapCenterValue - 446518,
    fullRecordGapCenterValue - 446308,
    fullRecordGapCenterValue - 446122,
    fullRecordGapCenterValue - 446074,
    fullRecordGapCenterValue - 446038,
    fullRecordGapCenterValue - 445948,
    fullRecordGapCenterValue - 445870,
    fullRecordGapCenterValue - 445864,
    fullRecordGapCenterValue - 445722,
    fullRecordGapCenterValue - 445674,
    fullRecordGapCenterValue - 445630,
    fullRecordGapCenterValue - 445528,
    fullRecordGapCenterValue - 445500,
    fullRecordGapCenterValue - 445330,
    fullRecordGapCenterValue - 445318,
    fullRecordGapCenterValue - 445294,
    fullRecordGapCenterValue - 445288,
    fullRecordGapCenterValue - 445182,
    fullRecordGapCenterValue - 445062,
    fullRecordGapCenterValue - 445002,
    fullRecordGapCenterValue - 444922]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00002_fermat : ∀ n ∈ fullRecordGapRow00002_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00065_not_prime : ¬(recordGapCenter - 450292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450292]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00066_not_prime : ¬(recordGapCenter - 450174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450174]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00067_not_prime : ¬(recordGapCenter - 450154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450154]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00068_not_prime : ¬(recordGapCenter - 450130).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450130]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00069_not_prime : ¬(recordGapCenter - 450078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450078]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00070_not_prime : ¬(recordGapCenter - 450004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 450004]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00071_not_prime : ¬(recordGapCenter - 449782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 449782]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00072_not_prime : ¬(recordGapCenter - 449710).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 449710]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00073_not_prime : ¬(recordGapCenter - 449518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 449518]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00074_not_prime : ¬(recordGapCenter - 449368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 449368]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00075_not_prime : ¬(recordGapCenter - 449188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 449188]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00076_not_prime : ¬(recordGapCenter - 448984).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448984]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00077_not_prime : ¬(recordGapCenter - 448962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448962]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00078_not_prime : ¬(recordGapCenter - 448852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448852]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00079_not_prime : ¬(recordGapCenter - 448828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448828]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00080_not_prime : ¬(recordGapCenter - 448648).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448648]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00081_not_prime : ¬(recordGapCenter - 448534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448534]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00082_not_prime : ¬(recordGapCenter - 448444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448444]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00083_not_prime : ¬(recordGapCenter - 448348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448348]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00084_not_prime : ¬(recordGapCenter - 448278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448278]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00085_not_prime : ¬(recordGapCenter - 448258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448258]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00086_not_prime : ¬(recordGapCenter - 448138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448138]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00087_not_prime : ¬(recordGapCenter - 448072).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448072]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00088_not_prime : ¬(recordGapCenter - 448054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 448054]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00089_not_prime : ¬(recordGapCenter - 447970).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 447970]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00090_not_prime : ¬(recordGapCenter - 447838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 447838]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00091_not_prime : ¬(recordGapCenter - 447730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 447730]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00092_not_prime : ¬(recordGapCenter - 447652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 447652]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00093_not_prime : ¬(recordGapCenter - 447592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 447592]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00094_not_prime : ¬(recordGapCenter - 447514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 447514]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00095_not_prime : ¬(recordGapCenter - 447394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 447394]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00096_not_prime : ¬(recordGapCenter - 447334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 447334]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00097_not_prime : ¬(recordGapCenter - 447208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 447208]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00098_not_prime : ¬(recordGapCenter - 447058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 447058]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00099_not_prime : ¬(recordGapCenter - 447054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 447054]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00100_not_prime : ¬(recordGapCenter - 446968).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 446968]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00101_not_prime : ¬(recordGapCenter - 446962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 446962]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00102_not_prime : ¬(recordGapCenter - 446938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 446938]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00103_not_prime : ¬(recordGapCenter - 446932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 446932]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00104_not_prime : ¬(recordGapCenter - 446878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 446878]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00105_not_prime : ¬(recordGapCenter - 446722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 446722]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00106_not_prime : ¬(recordGapCenter - 446718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 446718]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00107_not_prime : ¬(recordGapCenter - 446694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 446694]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00108_not_prime : ¬(recordGapCenter - 446518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 446518]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00109_not_prime : ¬(recordGapCenter - 446308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 446308]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00110_not_prime : ¬(recordGapCenter - 446122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 446122]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00111_not_prime : ¬(recordGapCenter - 446074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 446074]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00112_not_prime : ¬(recordGapCenter - 446038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 446038]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00113_not_prime : ¬(recordGapCenter - 445948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445948]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00114_not_prime : ¬(recordGapCenter - 445870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445870]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00115_not_prime : ¬(recordGapCenter - 445864).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445864]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00116_not_prime : ¬(recordGapCenter - 445722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445722]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00117_not_prime : ¬(recordGapCenter - 445674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445674]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00118_not_prime : ¬(recordGapCenter - 445630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445630]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00119_not_prime : ¬(recordGapCenter - 445528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445528]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00120_not_prime : ¬(recordGapCenter - 445500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445500]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00121_not_prime : ¬(recordGapCenter - 445330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445330]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00122_not_prime : ¬(recordGapCenter - 445318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445318]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00123_not_prime : ¬(recordGapCenter - 445294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445294]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00124_not_prime : ¬(recordGapCenter - 445288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445288]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00125_not_prime : ¬(recordGapCenter - 445182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445182]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00126_not_prime : ¬(recordGapCenter - 445062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445062]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00127_not_prime : ¬(recordGapCenter - 445002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 445002]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

theorem fullRecordGapTerm00128_not_prime : ¬(recordGapCenter - 444922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 444922]
  · apply fullRecordGapRow00002_fermat
    simp [fullRecordGapRow00002_values]

end PrimeFactorUnimodality
