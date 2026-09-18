import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00018_values : List Nat :=
  [fullRecordGapCenterValue - 369154,
    fullRecordGapCenterValue - 369114,
    fullRecordGapCenterValue - 369022,
    fullRecordGapCenterValue - 368974,
    fullRecordGapCenterValue - 368818,
    fullRecordGapCenterValue - 368778,
    fullRecordGapCenterValue - 368692,
    fullRecordGapCenterValue - 368674,
    fullRecordGapCenterValue - 368584,
    fullRecordGapCenterValue - 368518,
    fullRecordGapCenterValue - 368422,
    fullRecordGapCenterValue - 368398,
    fullRecordGapCenterValue - 368374,
    fullRecordGapCenterValue - 368332,
    fullRecordGapCenterValue - 368314,
    fullRecordGapCenterValue - 368308,
    fullRecordGapCenterValue - 368164,
    fullRecordGapCenterValue - 368062,
    fullRecordGapCenterValue - 368058,
    fullRecordGapCenterValue - 368034,
    fullRecordGapCenterValue - 368014,
    fullRecordGapCenterValue - 367918,
    fullRecordGapCenterValue - 367912,
    fullRecordGapCenterValue - 367762,
    fullRecordGapCenterValue - 367672,
    fullRecordGapCenterValue - 367594,
    fullRecordGapCenterValue - 367204,
    fullRecordGapCenterValue - 367084,
    fullRecordGapCenterValue - 367012,
    fullRecordGapCenterValue - 366994,
    fullRecordGapCenterValue - 366922,
    fullRecordGapCenterValue - 366844,
    fullRecordGapCenterValue - 366774,
    fullRecordGapCenterValue - 366594,
    fullRecordGapCenterValue - 366382,
    fullRecordGapCenterValue - 366342,
    fullRecordGapCenterValue - 366232,
    fullRecordGapCenterValue - 366162,
    fullRecordGapCenterValue - 366082,
    fullRecordGapCenterValue - 366042,
    fullRecordGapCenterValue - 365998,
    fullRecordGapCenterValue - 365962,
    fullRecordGapCenterValue - 365572,
    fullRecordGapCenterValue - 365538,
    fullRecordGapCenterValue - 365502,
    fullRecordGapCenterValue - 365374,
    fullRecordGapCenterValue - 365322,
    fullRecordGapCenterValue - 365278,
    fullRecordGapCenterValue - 365214,
    fullRecordGapCenterValue - 365188,
    fullRecordGapCenterValue - 365098,
    fullRecordGapCenterValue - 364972,
    fullRecordGapCenterValue - 364948,
    fullRecordGapCenterValue - 364674,
    fullRecordGapCenterValue - 364618,
    fullRecordGapCenterValue - 364552,
    fullRecordGapCenterValue - 364542,
    fullRecordGapCenterValue - 364422,
    fullRecordGapCenterValue - 364222,
    fullRecordGapCenterValue - 364198,
    fullRecordGapCenterValue - 364054,
    fullRecordGapCenterValue - 364024,
    fullRecordGapCenterValue - 363954,
    fullRecordGapCenterValue - 363934]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00018_fermat : ∀ n ∈ fullRecordGapRow00018_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01089_not_prime : ¬(recordGapCenter - 369154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369154]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01090_not_prime : ¬(recordGapCenter - 369114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369114]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01091_not_prime : ¬(recordGapCenter - 369022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369022]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01092_not_prime : ¬(recordGapCenter - 368974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368974]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01093_not_prime : ¬(recordGapCenter - 368818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368818]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01094_not_prime : ¬(recordGapCenter - 368778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368778]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01095_not_prime : ¬(recordGapCenter - 368692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368692]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01096_not_prime : ¬(recordGapCenter - 368674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368674]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01097_not_prime : ¬(recordGapCenter - 368584).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368584]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01098_not_prime : ¬(recordGapCenter - 368518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368518]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01099_not_prime : ¬(recordGapCenter - 368422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368422]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01100_not_prime : ¬(recordGapCenter - 368398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368398]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01101_not_prime : ¬(recordGapCenter - 368374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368374]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01102_not_prime : ¬(recordGapCenter - 368332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368332]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01103_not_prime : ¬(recordGapCenter - 368314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368314]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01104_not_prime : ¬(recordGapCenter - 368308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368308]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01105_not_prime : ¬(recordGapCenter - 368164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368164]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01106_not_prime : ¬(recordGapCenter - 368062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368062]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01107_not_prime : ¬(recordGapCenter - 368058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368058]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01108_not_prime : ¬(recordGapCenter - 368034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368034]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01109_not_prime : ¬(recordGapCenter - 368014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368014]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01110_not_prime : ¬(recordGapCenter - 367918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367918]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01111_not_prime : ¬(recordGapCenter - 367912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367912]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01112_not_prime : ¬(recordGapCenter - 367762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367762]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01113_not_prime : ¬(recordGapCenter - 367672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367672]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01114_not_prime : ¬(recordGapCenter - 367594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367594]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01115_not_prime : ¬(recordGapCenter - 367204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367204]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01116_not_prime : ¬(recordGapCenter - 367084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367084]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01117_not_prime : ¬(recordGapCenter - 367012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367012]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01118_not_prime : ¬(recordGapCenter - 366994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366994]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01119_not_prime : ¬(recordGapCenter - 366922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366922]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01120_not_prime : ¬(recordGapCenter - 366844).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366844]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01121_not_prime : ¬(recordGapCenter - 366774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366774]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01122_not_prime : ¬(recordGapCenter - 366594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366594]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01123_not_prime : ¬(recordGapCenter - 366382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366382]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01124_not_prime : ¬(recordGapCenter - 366342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366342]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01125_not_prime : ¬(recordGapCenter - 366232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366232]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01126_not_prime : ¬(recordGapCenter - 366162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366162]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01127_not_prime : ¬(recordGapCenter - 366082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366082]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01128_not_prime : ¬(recordGapCenter - 366042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366042]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01129_not_prime : ¬(recordGapCenter - 365998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365998]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01130_not_prime : ¬(recordGapCenter - 365962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365962]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01131_not_prime : ¬(recordGapCenter - 365572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365572]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01132_not_prime : ¬(recordGapCenter - 365538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365538]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01133_not_prime : ¬(recordGapCenter - 365502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365502]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01134_not_prime : ¬(recordGapCenter - 365374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365374]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01135_not_prime : ¬(recordGapCenter - 365322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365322]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01136_not_prime : ¬(recordGapCenter - 365278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365278]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01137_not_prime : ¬(recordGapCenter - 365214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365214]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01138_not_prime : ¬(recordGapCenter - 365188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365188]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01139_not_prime : ¬(recordGapCenter - 365098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365098]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01140_not_prime : ¬(recordGapCenter - 364972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364972]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01141_not_prime : ¬(recordGapCenter - 364948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364948]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01142_not_prime : ¬(recordGapCenter - 364674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364674]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01143_not_prime : ¬(recordGapCenter - 364618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364618]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01144_not_prime : ¬(recordGapCenter - 364552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364552]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01145_not_prime : ¬(recordGapCenter - 364542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364542]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01146_not_prime : ¬(recordGapCenter - 364422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364422]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01147_not_prime : ¬(recordGapCenter - 364222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364222]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01148_not_prime : ¬(recordGapCenter - 364198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364198]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01149_not_prime : ¬(recordGapCenter - 364054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364054]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01150_not_prime : ¬(recordGapCenter - 364024).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364024]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01151_not_prime : ¬(recordGapCenter - 363954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363954]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

theorem fullRecordGapTerm01152_not_prime : ¬(recordGapCenter - 363934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363934]
  · apply fullRecordGapRow00018_fermat
    simp [fullRecordGapRow00018_values]

end PrimeFactorUnimodality
