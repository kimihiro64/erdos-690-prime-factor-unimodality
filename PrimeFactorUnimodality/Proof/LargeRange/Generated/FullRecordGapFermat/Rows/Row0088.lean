import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00088_values : List Nat :=
  [fullRecordGapCenterValue + 281102,
    fullRecordGapCenterValue + 281166,
    fullRecordGapCenterValue + 281202,
    fullRecordGapCenterValue + 281262,
    fullRecordGapCenterValue + 281318,
    fullRecordGapCenterValue + 281366,
    fullRecordGapCenterValue + 281492,
    fullRecordGapCenterValue + 281600,
    fullRecordGapCenterValue + 281678,
    fullRecordGapCenterValue + 281982,
    fullRecordGapCenterValue + 282122,
    fullRecordGapCenterValue + 282242,
    fullRecordGapCenterValue + 282306,
    fullRecordGapCenterValue + 282398,
    fullRecordGapCenterValue + 282482,
    fullRecordGapCenterValue + 282566,
    fullRecordGapCenterValue + 282836,
    fullRecordGapCenterValue + 282858,
    fullRecordGapCenterValue + 282966,
    fullRecordGapCenterValue + 283076,
    fullRecordGapCenterValue + 283238,
    fullRecordGapCenterValue + 283242,
    fullRecordGapCenterValue + 283298,
    fullRecordGapCenterValue + 283358,
    fullRecordGapCenterValue + 283418,
    fullRecordGapCenterValue + 283500,
    fullRecordGapCenterValue + 283586,
    fullRecordGapCenterValue + 283622,
    fullRecordGapCenterValue + 283658,
    fullRecordGapCenterValue + 283676,
    fullRecordGapCenterValue + 283706,
    fullRecordGapCenterValue + 283742,
    fullRecordGapCenterValue + 283748,
    fullRecordGapCenterValue + 283782,
    fullRecordGapCenterValue + 283902,
    fullRecordGapCenterValue + 283916,
    fullRecordGapCenterValue + 283922,
    fullRecordGapCenterValue + 283988,
    fullRecordGapCenterValue + 284156,
    fullRecordGapCenterValue + 284198,
    fullRecordGapCenterValue + 284222,
    fullRecordGapCenterValue + 284322,
    fullRecordGapCenterValue + 284516,
    fullRecordGapCenterValue + 284646,
    fullRecordGapCenterValue + 284762,
    fullRecordGapCenterValue + 284996,
    fullRecordGapCenterValue + 285078,
    fullRecordGapCenterValue + 285086,
    fullRecordGapCenterValue + 285120,
    fullRecordGapCenterValue + 285126,
    fullRecordGapCenterValue + 285146,
    fullRecordGapCenterValue + 285162,
    fullRecordGapCenterValue + 285198,
    fullRecordGapCenterValue + 285356,
    fullRecordGapCenterValue + 285378,
    fullRecordGapCenterValue + 285422,
    fullRecordGapCenterValue + 285518,
    fullRecordGapCenterValue + 285542,
    fullRecordGapCenterValue + 285596,
    fullRecordGapCenterValue + 285716,
    fullRecordGapCenterValue + 285768,
    fullRecordGapCenterValue + 285932,
    fullRecordGapCenterValue + 285962,
    fullRecordGapCenterValue + 286196]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00088_fermat : ∀ n ∈ fullRecordGapRow00088_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05569_not_prime : ¬(recordGapCenter + 281102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 281102]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05570_not_prime : ¬(recordGapCenter + 281166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 281166]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05571_not_prime : ¬(recordGapCenter + 281202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 281202]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05572_not_prime : ¬(recordGapCenter + 281262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 281262]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05573_not_prime : ¬(recordGapCenter + 281318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 281318]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05574_not_prime : ¬(recordGapCenter + 281366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 281366]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05575_not_prime : ¬(recordGapCenter + 281492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 281492]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05576_not_prime : ¬(recordGapCenter + 281600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 281600]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05577_not_prime : ¬(recordGapCenter + 281678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 281678]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05578_not_prime : ¬(recordGapCenter + 281982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 281982]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05579_not_prime : ¬(recordGapCenter + 282122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 282122]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05580_not_prime : ¬(recordGapCenter + 282242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 282242]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05581_not_prime : ¬(recordGapCenter + 282306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 282306]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05582_not_prime : ¬(recordGapCenter + 282398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 282398]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05583_not_prime : ¬(recordGapCenter + 282482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 282482]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05584_not_prime : ¬(recordGapCenter + 282566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 282566]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05585_not_prime : ¬(recordGapCenter + 282836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 282836]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05586_not_prime : ¬(recordGapCenter + 282858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 282858]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05587_not_prime : ¬(recordGapCenter + 282966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 282966]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05588_not_prime : ¬(recordGapCenter + 283076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283076]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05589_not_prime : ¬(recordGapCenter + 283238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283238]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05590_not_prime : ¬(recordGapCenter + 283242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283242]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05591_not_prime : ¬(recordGapCenter + 283298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283298]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05592_not_prime : ¬(recordGapCenter + 283358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283358]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05593_not_prime : ¬(recordGapCenter + 283418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283418]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05594_not_prime : ¬(recordGapCenter + 283500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283500]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05595_not_prime : ¬(recordGapCenter + 283586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283586]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05596_not_prime : ¬(recordGapCenter + 283622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283622]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05597_not_prime : ¬(recordGapCenter + 283658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283658]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05598_not_prime : ¬(recordGapCenter + 283676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283676]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05599_not_prime : ¬(recordGapCenter + 283706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283706]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05600_not_prime : ¬(recordGapCenter + 283742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283742]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05601_not_prime : ¬(recordGapCenter + 283748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283748]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05602_not_prime : ¬(recordGapCenter + 283782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283782]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05603_not_prime : ¬(recordGapCenter + 283902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283902]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05604_not_prime : ¬(recordGapCenter + 283916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283916]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05605_not_prime : ¬(recordGapCenter + 283922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283922]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05606_not_prime : ¬(recordGapCenter + 283988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 283988]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05607_not_prime : ¬(recordGapCenter + 284156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 284156]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05608_not_prime : ¬(recordGapCenter + 284198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 284198]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05609_not_prime : ¬(recordGapCenter + 284222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 284222]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05610_not_prime : ¬(recordGapCenter + 284322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 284322]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05611_not_prime : ¬(recordGapCenter + 284516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 284516]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05612_not_prime : ¬(recordGapCenter + 284646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 284646]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05613_not_prime : ¬(recordGapCenter + 284762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 284762]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05614_not_prime : ¬(recordGapCenter + 284996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 284996]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05615_not_prime : ¬(recordGapCenter + 285078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285078]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05616_not_prime : ¬(recordGapCenter + 285086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285086]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05617_not_prime : ¬(recordGapCenter + 285120).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285120]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05618_not_prime : ¬(recordGapCenter + 285126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285126]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05619_not_prime : ¬(recordGapCenter + 285146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285146]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05620_not_prime : ¬(recordGapCenter + 285162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285162]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05621_not_prime : ¬(recordGapCenter + 285198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285198]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05622_not_prime : ¬(recordGapCenter + 285356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285356]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05623_not_prime : ¬(recordGapCenter + 285378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285378]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05624_not_prime : ¬(recordGapCenter + 285422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285422]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05625_not_prime : ¬(recordGapCenter + 285518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285518]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05626_not_prime : ¬(recordGapCenter + 285542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285542]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05627_not_prime : ¬(recordGapCenter + 285596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285596]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05628_not_prime : ¬(recordGapCenter + 285716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285716]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05629_not_prime : ¬(recordGapCenter + 285768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285768]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05630_not_prime : ¬(recordGapCenter + 285932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285932]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05631_not_prime : ¬(recordGapCenter + 285962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 285962]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

theorem fullRecordGapTerm05632_not_prime : ¬(recordGapCenter + 286196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 286196]
  · apply fullRecordGapRow00088_fermat
    simp [fullRecordGapRow00088_values]

end PrimeFactorUnimodality
