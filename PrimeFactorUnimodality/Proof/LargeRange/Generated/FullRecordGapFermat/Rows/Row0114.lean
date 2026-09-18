import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00114_values : List Nat :=
  [fullRecordGapCenterValue + 412268,
    fullRecordGapCenterValue + 412358,
    fullRecordGapCenterValue + 412382,
    fullRecordGapCenterValue + 412406,
    fullRecordGapCenterValue + 412458,
    fullRecordGapCenterValue + 412766,
    fullRecordGapCenterValue + 412878,
    fullRecordGapCenterValue + 412926,
    fullRecordGapCenterValue + 413102,
    fullRecordGapCenterValue + 413228,
    fullRecordGapCenterValue + 413246,
    fullRecordGapCenterValue + 413276,
    fullRecordGapCenterValue + 413346,
    fullRecordGapCenterValue + 413396,
    fullRecordGapCenterValue + 413432,
    fullRecordGapCenterValue + 413498,
    fullRecordGapCenterValue + 413528,
    fullRecordGapCenterValue + 413558,
    fullRecordGapCenterValue + 413642,
    fullRecordGapCenterValue + 413682,
    fullRecordGapCenterValue + 413768,
    fullRecordGapCenterValue + 413778,
    fullRecordGapCenterValue + 414296,
    fullRecordGapCenterValue + 414338,
    fullRecordGapCenterValue + 414402,
    fullRecordGapCenterValue + 414632,
    fullRecordGapCenterValue + 414818,
    fullRecordGapCenterValue + 414962,
    fullRecordGapCenterValue + 414978,
    fullRecordGapCenterValue + 415082,
    fullRecordGapCenterValue + 415146,
    fullRecordGapCenterValue + 415238,
    fullRecordGapCenterValue + 415256,
    fullRecordGapCenterValue + 415322,
    fullRecordGapCenterValue + 415622,
    fullRecordGapCenterValue + 415902,
    fullRecordGapCenterValue + 415916,
    fullRecordGapCenterValue + 416018,
    fullRecordGapCenterValue + 416022,
    fullRecordGapCenterValue + 416298,
    fullRecordGapCenterValue + 416348,
    fullRecordGapCenterValue + 416378,
    fullRecordGapCenterValue + 416418,
    fullRecordGapCenterValue + 416462,
    fullRecordGapCenterValue + 416582,
    fullRecordGapCenterValue + 416586,
    fullRecordGapCenterValue + 416666,
    fullRecordGapCenterValue + 416732,
    fullRecordGapCenterValue + 416882,
    fullRecordGapCenterValue + 416886,
    fullRecordGapCenterValue + 416946,
    fullRecordGapCenterValue + 416972,
    fullRecordGapCenterValue + 417002,
    fullRecordGapCenterValue + 417176,
    fullRecordGapCenterValue + 417188,
    fullRecordGapCenterValue + 417308,
    fullRecordGapCenterValue + 417476,
    fullRecordGapCenterValue + 417518,
    fullRecordGapCenterValue + 417572,
    fullRecordGapCenterValue + 417866,
    fullRecordGapCenterValue + 417926,
    fullRecordGapCenterValue + 417966,
    fullRecordGapCenterValue + 417986,
    fullRecordGapCenterValue + 418058]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00114_fermat : ∀ n ∈ fullRecordGapRow00114_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07233_not_prime : ¬(recordGapCenter + 412268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 412268]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07234_not_prime : ¬(recordGapCenter + 412358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 412358]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07235_not_prime : ¬(recordGapCenter + 412382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 412382]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07236_not_prime : ¬(recordGapCenter + 412406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 412406]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07237_not_prime : ¬(recordGapCenter + 412458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 412458]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07238_not_prime : ¬(recordGapCenter + 412766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 412766]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07239_not_prime : ¬(recordGapCenter + 412878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 412878]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07240_not_prime : ¬(recordGapCenter + 412926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 412926]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07241_not_prime : ¬(recordGapCenter + 413102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 413102]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07242_not_prime : ¬(recordGapCenter + 413228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 413228]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07243_not_prime : ¬(recordGapCenter + 413246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 413246]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07244_not_prime : ¬(recordGapCenter + 413276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 413276]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07245_not_prime : ¬(recordGapCenter + 413346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 413346]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07246_not_prime : ¬(recordGapCenter + 413396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 413396]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07247_not_prime : ¬(recordGapCenter + 413432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 413432]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07248_not_prime : ¬(recordGapCenter + 413498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 413498]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07249_not_prime : ¬(recordGapCenter + 413528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 413528]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07250_not_prime : ¬(recordGapCenter + 413558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 413558]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07251_not_prime : ¬(recordGapCenter + 413642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 413642]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07252_not_prime : ¬(recordGapCenter + 413682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 413682]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07253_not_prime : ¬(recordGapCenter + 413768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 413768]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07254_not_prime : ¬(recordGapCenter + 413778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 413778]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07255_not_prime : ¬(recordGapCenter + 414296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 414296]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07256_not_prime : ¬(recordGapCenter + 414338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 414338]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07257_not_prime : ¬(recordGapCenter + 414402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 414402]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07258_not_prime : ¬(recordGapCenter + 414632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 414632]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07259_not_prime : ¬(recordGapCenter + 414818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 414818]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07260_not_prime : ¬(recordGapCenter + 414962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 414962]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07261_not_prime : ¬(recordGapCenter + 414978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 414978]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07262_not_prime : ¬(recordGapCenter + 415082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 415082]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07263_not_prime : ¬(recordGapCenter + 415146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 415146]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07264_not_prime : ¬(recordGapCenter + 415238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 415238]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07265_not_prime : ¬(recordGapCenter + 415256).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 415256]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07266_not_prime : ¬(recordGapCenter + 415322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 415322]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07267_not_prime : ¬(recordGapCenter + 415622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 415622]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07268_not_prime : ¬(recordGapCenter + 415902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 415902]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07269_not_prime : ¬(recordGapCenter + 415916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 415916]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07270_not_prime : ¬(recordGapCenter + 416018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416018]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07271_not_prime : ¬(recordGapCenter + 416022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416022]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07272_not_prime : ¬(recordGapCenter + 416298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416298]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07273_not_prime : ¬(recordGapCenter + 416348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416348]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07274_not_prime : ¬(recordGapCenter + 416378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416378]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07275_not_prime : ¬(recordGapCenter + 416418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416418]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07276_not_prime : ¬(recordGapCenter + 416462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416462]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07277_not_prime : ¬(recordGapCenter + 416582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416582]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07278_not_prime : ¬(recordGapCenter + 416586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416586]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07279_not_prime : ¬(recordGapCenter + 416666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416666]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07280_not_prime : ¬(recordGapCenter + 416732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416732]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07281_not_prime : ¬(recordGapCenter + 416882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416882]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07282_not_prime : ¬(recordGapCenter + 416886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416886]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07283_not_prime : ¬(recordGapCenter + 416946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416946]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07284_not_prime : ¬(recordGapCenter + 416972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 416972]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07285_not_prime : ¬(recordGapCenter + 417002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 417002]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07286_not_prime : ¬(recordGapCenter + 417176).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 417176]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07287_not_prime : ¬(recordGapCenter + 417188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 417188]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07288_not_prime : ¬(recordGapCenter + 417308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 417308]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07289_not_prime : ¬(recordGapCenter + 417476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 417476]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07290_not_prime : ¬(recordGapCenter + 417518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 417518]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07291_not_prime : ¬(recordGapCenter + 417572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 417572]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07292_not_prime : ¬(recordGapCenter + 417866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 417866]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07293_not_prime : ¬(recordGapCenter + 417926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 417926]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07294_not_prime : ¬(recordGapCenter + 417966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 417966]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07295_not_prime : ¬(recordGapCenter + 417986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 417986]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

theorem fullRecordGapTerm07296_not_prime : ¬(recordGapCenter + 418058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 418058]
  · apply fullRecordGapRow00114_fermat
    simp [fullRecordGapRow00114_values]

end PrimeFactorUnimodality
