import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00100_values : List Nat :=
  [fullRecordGapCenterValue + 343698,
    fullRecordGapCenterValue + 343778,
    fullRecordGapCenterValue + 343806,
    fullRecordGapCenterValue + 344082,
    fullRecordGapCenterValue + 344108,
    fullRecordGapCenterValue + 344138,
    fullRecordGapCenterValue + 344202,
    fullRecordGapCenterValue + 344306,
    fullRecordGapCenterValue + 344342,
    fullRecordGapCenterValue + 344438,
    fullRecordGapCenterValue + 344478,
    fullRecordGapCenterValue + 344486,
    fullRecordGapCenterValue + 344562,
    fullRecordGapCenterValue + 344642,
    fullRecordGapCenterValue + 344822,
    fullRecordGapCenterValue + 344922,
    fullRecordGapCenterValue + 344960,
    fullRecordGapCenterValue + 344996,
    fullRecordGapCenterValue + 345018,
    fullRecordGapCenterValue + 345038,
    fullRecordGapCenterValue + 345188,
    fullRecordGapCenterValue + 345206,
    fullRecordGapCenterValue + 345272,
    fullRecordGapCenterValue + 345416,
    fullRecordGapCenterValue + 345522,
    fullRecordGapCenterValue + 345602,
    fullRecordGapCenterValue + 345608,
    fullRecordGapCenterValue + 345866,
    fullRecordGapCenterValue + 345896,
    fullRecordGapCenterValue + 345908,
    fullRecordGapCenterValue + 345938,
    fullRecordGapCenterValue + 345986,
    fullRecordGapCenterValue + 346046,
    fullRecordGapCenterValue + 346088,
    fullRecordGapCenterValue + 346278,
    fullRecordGapCenterValue + 346362,
    fullRecordGapCenterValue + 346418,
    fullRecordGapCenterValue + 346586,
    fullRecordGapCenterValue + 346686,
    fullRecordGapCenterValue + 346722,
    fullRecordGapCenterValue + 346746,
    fullRecordGapCenterValue + 346946,
    fullRecordGapCenterValue + 347012,
    fullRecordGapCenterValue + 347118,
    fullRecordGapCenterValue + 347252,
    fullRecordGapCenterValue + 347342,
    fullRecordGapCenterValue + 347348,
    fullRecordGapCenterValue + 347366,
    fullRecordGapCenterValue + 347372,
    fullRecordGapCenterValue + 347406,
    fullRecordGapCenterValue + 347502,
    fullRecordGapCenterValue + 347558,
    fullRecordGapCenterValue + 347658,
    fullRecordGapCenterValue + 347756,
    fullRecordGapCenterValue + 347846,
    fullRecordGapCenterValue + 347862,
    fullRecordGapCenterValue + 347876,
    fullRecordGapCenterValue + 347946,
    fullRecordGapCenterValue + 347972,
    fullRecordGapCenterValue + 348078,
    fullRecordGapCenterValue + 348122,
    fullRecordGapCenterValue + 348162,
    fullRecordGapCenterValue + 348182,
    fullRecordGapCenterValue + 348338]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00100_fermat : ∀ n ∈ fullRecordGapRow00100_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06337_not_prime : ¬(recordGapCenter + 343698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 343698]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06338_not_prime : ¬(recordGapCenter + 343778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 343778]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06339_not_prime : ¬(recordGapCenter + 343806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 343806]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06340_not_prime : ¬(recordGapCenter + 344082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344082]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06341_not_prime : ¬(recordGapCenter + 344108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344108]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06342_not_prime : ¬(recordGapCenter + 344138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344138]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06343_not_prime : ¬(recordGapCenter + 344202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344202]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06344_not_prime : ¬(recordGapCenter + 344306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344306]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06345_not_prime : ¬(recordGapCenter + 344342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344342]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06346_not_prime : ¬(recordGapCenter + 344438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344438]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06347_not_prime : ¬(recordGapCenter + 344478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344478]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06348_not_prime : ¬(recordGapCenter + 344486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344486]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06349_not_prime : ¬(recordGapCenter + 344562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344562]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06350_not_prime : ¬(recordGapCenter + 344642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344642]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06351_not_prime : ¬(recordGapCenter + 344822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344822]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06352_not_prime : ¬(recordGapCenter + 344922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344922]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06353_not_prime : ¬(recordGapCenter + 344960).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344960]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06354_not_prime : ¬(recordGapCenter + 344996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 344996]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06355_not_prime : ¬(recordGapCenter + 345018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 345018]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06356_not_prime : ¬(recordGapCenter + 345038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 345038]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06357_not_prime : ¬(recordGapCenter + 345188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 345188]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06358_not_prime : ¬(recordGapCenter + 345206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 345206]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06359_not_prime : ¬(recordGapCenter + 345272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 345272]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06360_not_prime : ¬(recordGapCenter + 345416).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 345416]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06361_not_prime : ¬(recordGapCenter + 345522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 345522]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06362_not_prime : ¬(recordGapCenter + 345602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 345602]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06363_not_prime : ¬(recordGapCenter + 345608).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 345608]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06364_not_prime : ¬(recordGapCenter + 345866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 345866]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06365_not_prime : ¬(recordGapCenter + 345896).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 345896]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06366_not_prime : ¬(recordGapCenter + 345908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 345908]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06367_not_prime : ¬(recordGapCenter + 345938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 345938]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06368_not_prime : ¬(recordGapCenter + 345986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 345986]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06369_not_prime : ¬(recordGapCenter + 346046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 346046]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06370_not_prime : ¬(recordGapCenter + 346088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 346088]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06371_not_prime : ¬(recordGapCenter + 346278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 346278]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06372_not_prime : ¬(recordGapCenter + 346362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 346362]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06373_not_prime : ¬(recordGapCenter + 346418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 346418]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06374_not_prime : ¬(recordGapCenter + 346586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 346586]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06375_not_prime : ¬(recordGapCenter + 346686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 346686]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06376_not_prime : ¬(recordGapCenter + 346722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 346722]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06377_not_prime : ¬(recordGapCenter + 346746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 346746]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06378_not_prime : ¬(recordGapCenter + 346946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 346946]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06379_not_prime : ¬(recordGapCenter + 347012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347012]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06380_not_prime : ¬(recordGapCenter + 347118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347118]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06381_not_prime : ¬(recordGapCenter + 347252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347252]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06382_not_prime : ¬(recordGapCenter + 347342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347342]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06383_not_prime : ¬(recordGapCenter + 347348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347348]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06384_not_prime : ¬(recordGapCenter + 347366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347366]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06385_not_prime : ¬(recordGapCenter + 347372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347372]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06386_not_prime : ¬(recordGapCenter + 347406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347406]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06387_not_prime : ¬(recordGapCenter + 347502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347502]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06388_not_prime : ¬(recordGapCenter + 347558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347558]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06389_not_prime : ¬(recordGapCenter + 347658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347658]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06390_not_prime : ¬(recordGapCenter + 347756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347756]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06391_not_prime : ¬(recordGapCenter + 347846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347846]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06392_not_prime : ¬(recordGapCenter + 347862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347862]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06393_not_prime : ¬(recordGapCenter + 347876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347876]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06394_not_prime : ¬(recordGapCenter + 347946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347946]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06395_not_prime : ¬(recordGapCenter + 347972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 347972]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06396_not_prime : ¬(recordGapCenter + 348078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348078]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06397_not_prime : ¬(recordGapCenter + 348122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348122]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06398_not_prime : ¬(recordGapCenter + 348162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348162]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06399_not_prime : ¬(recordGapCenter + 348182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348182]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

theorem fullRecordGapTerm06400_not_prime : ¬(recordGapCenter + 348338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 348338]
  · apply fullRecordGapRow00100_fermat
    simp [fullRecordGapRow00100_values]

end PrimeFactorUnimodality
