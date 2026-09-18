import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00072_values : List Nat :=
  [fullRecordGapCenterValue + 168842,
    fullRecordGapCenterValue + 168926,
    fullRecordGapCenterValue + 168960,
    fullRecordGapCenterValue + 168962,
    fullRecordGapCenterValue + 169046,
    fullRecordGapCenterValue + 169382,
    fullRecordGapCenterValue + 169586,
    fullRecordGapCenterValue + 169982,
    fullRecordGapCenterValue + 170042,
    fullRecordGapCenterValue + 170318,
    fullRecordGapCenterValue + 170426,
    fullRecordGapCenterValue + 170726,
    fullRecordGapCenterValue + 171278,
    fullRecordGapCenterValue + 171638,
    fullRecordGapCenterValue + 171686,
    fullRecordGapCenterValue + 171818,
    fullRecordGapCenterValue + 171866,
    fullRecordGapCenterValue + 171998,
    fullRecordGapCenterValue + 172032,
    fullRecordGapCenterValue + 172226,
    fullRecordGapCenterValue + 172358,
    fullRecordGapCenterValue + 172532,
    fullRecordGapCenterValue + 172538,
    fullRecordGapCenterValue + 172622,
    fullRecordGapCenterValue + 172646,
    fullRecordGapCenterValue + 172826,
    fullRecordGapCenterValue + 173078,
    fullRecordGapCenterValue + 173198,
    fullRecordGapCenterValue + 173486,
    fullRecordGapCenterValue + 173702,
    fullRecordGapCenterValue + 173738,
    fullRecordGapCenterValue + 173918,
    fullRecordGapCenterValue + 173948,
    fullRecordGapCenterValue + 174206,
    fullRecordGapCenterValue + 174240,
    fullRecordGapCenterValue + 174422,
    fullRecordGapCenterValue + 174806,
    fullRecordGapCenterValue + 175046,
    fullRecordGapCenterValue + 175166,
    fullRecordGapCenterValue + 175178,
    fullRecordGapCenterValue + 175298,
    fullRecordGapCenterValue + 175586,
    fullRecordGapCenterValue + 175616,
    fullRecordGapCenterValue + 175862,
    fullRecordGapCenterValue + 175892,
    fullRecordGapCenterValue + 175988,
    fullRecordGapCenterValue + 176186,
    fullRecordGapCenterValue + 176642,
    fullRecordGapCenterValue + 176846,
    fullRecordGapCenterValue + 177026,
    fullRecordGapCenterValue + 177116,
    fullRecordGapCenterValue + 177482,
    fullRecordGapCenterValue + 177746,
    fullRecordGapCenterValue + 178082,
    fullRecordGapCenterValue + 178202,
    fullRecordGapCenterValue + 178628,
    fullRecordGapCenterValue + 178742,
    fullRecordGapCenterValue + 178796,
    fullRecordGapCenterValue + 178826,
    fullRecordGapCenterValue + 179042,
    fullRecordGapCenterValue + 179198,
    fullRecordGapCenterValue + 179306,
    fullRecordGapCenterValue + 179342,
    fullRecordGapCenterValue + 179378]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00072_fermat : ∀ n ∈ fullRecordGapRow00072_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04545_not_prime : ¬(recordGapCenter + 168842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 168842]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04546_not_prime : ¬(recordGapCenter + 168926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 168926]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04547_not_prime : ¬(recordGapCenter + 168960).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 168960]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04548_not_prime : ¬(recordGapCenter + 168962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 168962]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04549_not_prime : ¬(recordGapCenter + 169046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 169046]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04550_not_prime : ¬(recordGapCenter + 169382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 169382]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04551_not_prime : ¬(recordGapCenter + 169586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 169586]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04552_not_prime : ¬(recordGapCenter + 169982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 169982]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04553_not_prime : ¬(recordGapCenter + 170042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 170042]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04554_not_prime : ¬(recordGapCenter + 170318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 170318]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04555_not_prime : ¬(recordGapCenter + 170426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 170426]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04556_not_prime : ¬(recordGapCenter + 170726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 170726]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04557_not_prime : ¬(recordGapCenter + 171278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 171278]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04558_not_prime : ¬(recordGapCenter + 171638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 171638]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04559_not_prime : ¬(recordGapCenter + 171686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 171686]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04560_not_prime : ¬(recordGapCenter + 171818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 171818]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04561_not_prime : ¬(recordGapCenter + 171866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 171866]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04562_not_prime : ¬(recordGapCenter + 171998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 171998]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04563_not_prime : ¬(recordGapCenter + 172032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172032]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04564_not_prime : ¬(recordGapCenter + 172226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172226]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04565_not_prime : ¬(recordGapCenter + 172358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172358]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04566_not_prime : ¬(recordGapCenter + 172532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172532]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04567_not_prime : ¬(recordGapCenter + 172538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172538]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04568_not_prime : ¬(recordGapCenter + 172622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172622]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04569_not_prime : ¬(recordGapCenter + 172646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172646]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04570_not_prime : ¬(recordGapCenter + 172826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 172826]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04571_not_prime : ¬(recordGapCenter + 173078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 173078]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04572_not_prime : ¬(recordGapCenter + 173198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 173198]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04573_not_prime : ¬(recordGapCenter + 173486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 173486]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04574_not_prime : ¬(recordGapCenter + 173702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 173702]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04575_not_prime : ¬(recordGapCenter + 173738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 173738]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04576_not_prime : ¬(recordGapCenter + 173918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 173918]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04577_not_prime : ¬(recordGapCenter + 173948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 173948]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04578_not_prime : ¬(recordGapCenter + 174206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 174206]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04579_not_prime : ¬(recordGapCenter + 174240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 174240]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04580_not_prime : ¬(recordGapCenter + 174422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 174422]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04581_not_prime : ¬(recordGapCenter + 174806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 174806]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04582_not_prime : ¬(recordGapCenter + 175046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175046]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04583_not_prime : ¬(recordGapCenter + 175166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175166]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04584_not_prime : ¬(recordGapCenter + 175178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175178]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04585_not_prime : ¬(recordGapCenter + 175298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175298]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04586_not_prime : ¬(recordGapCenter + 175586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175586]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04587_not_prime : ¬(recordGapCenter + 175616).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175616]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04588_not_prime : ¬(recordGapCenter + 175862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175862]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04589_not_prime : ¬(recordGapCenter + 175892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175892]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04590_not_prime : ¬(recordGapCenter + 175988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 175988]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04591_not_prime : ¬(recordGapCenter + 176186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 176186]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04592_not_prime : ¬(recordGapCenter + 176642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 176642]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04593_not_prime : ¬(recordGapCenter + 176846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 176846]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04594_not_prime : ¬(recordGapCenter + 177026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 177026]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04595_not_prime : ¬(recordGapCenter + 177116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 177116]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04596_not_prime : ¬(recordGapCenter + 177482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 177482]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04597_not_prime : ¬(recordGapCenter + 177746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 177746]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04598_not_prime : ¬(recordGapCenter + 178082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 178082]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04599_not_prime : ¬(recordGapCenter + 178202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 178202]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04600_not_prime : ¬(recordGapCenter + 178628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 178628]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04601_not_prime : ¬(recordGapCenter + 178742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 178742]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04602_not_prime : ¬(recordGapCenter + 178796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 178796]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04603_not_prime : ¬(recordGapCenter + 178826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 178826]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04604_not_prime : ¬(recordGapCenter + 179042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179042]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04605_not_prime : ¬(recordGapCenter + 179198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179198]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04606_not_prime : ¬(recordGapCenter + 179306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179306]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04607_not_prime : ¬(recordGapCenter + 179342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179342]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

theorem fullRecordGapTerm04608_not_prime : ¬(recordGapCenter + 179378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179378]
  · apply fullRecordGapRow00072_fermat
    simp [fullRecordGapRow00072_values]

end PrimeFactorUnimodality
