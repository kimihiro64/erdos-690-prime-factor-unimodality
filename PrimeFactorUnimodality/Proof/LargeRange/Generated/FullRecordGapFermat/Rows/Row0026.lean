import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00026_values : List Nat :=
  [fullRecordGapCenterValue - 327982,
    fullRecordGapCenterValue - 327802,
    fullRecordGapCenterValue - 327724,
    fullRecordGapCenterValue - 327718,
    fullRecordGapCenterValue - 327498,
    fullRecordGapCenterValue - 327462,
    fullRecordGapCenterValue - 327394,
    fullRecordGapCenterValue - 327388,
    fullRecordGapCenterValue - 327358,
    fullRecordGapCenterValue - 327322,
    fullRecordGapCenterValue - 327282,
    fullRecordGapCenterValue - 327274,
    fullRecordGapCenterValue - 327018,
    fullRecordGapCenterValue - 326994,
    fullRecordGapCenterValue - 326812,
    fullRecordGapCenterValue - 326734,
    fullRecordGapCenterValue - 326694,
    fullRecordGapCenterValue - 326514,
    fullRecordGapCenterValue - 326478,
    fullRecordGapCenterValue - 326422,
    fullRecordGapCenterValue - 326338,
    fullRecordGapCenterValue - 326254,
    fullRecordGapCenterValue - 326212,
    fullRecordGapCenterValue - 326202,
    fullRecordGapCenterValue - 326122,
    fullRecordGapCenterValue - 326038,
    fullRecordGapCenterValue - 325938,
    fullRecordGapCenterValue - 325828,
    fullRecordGapCenterValue - 325614,
    fullRecordGapCenterValue - 325498,
    fullRecordGapCenterValue - 325462,
    fullRecordGapCenterValue - 325372,
    fullRecordGapCenterValue - 325302,
    fullRecordGapCenterValue - 325282,
    fullRecordGapCenterValue - 325258,
    fullRecordGapCenterValue - 325132,
    fullRecordGapCenterValue - 325002,
    fullRecordGapCenterValue - 324798,
    fullRecordGapCenterValue - 324778,
    fullRecordGapCenterValue - 324718,
    fullRecordGapCenterValue - 324652,
    fullRecordGapCenterValue - 324628,
    fullRecordGapCenterValue - 324538,
    fullRecordGapCenterValue - 324498,
    fullRecordGapCenterValue - 324442,
    fullRecordGapCenterValue - 324354,
    fullRecordGapCenterValue - 324238,
    fullRecordGapCenterValue - 324172,
    fullRecordGapCenterValue - 324118,
    fullRecordGapCenterValue - 324078,
    fullRecordGapCenterValue - 324034,
    fullRecordGapCenterValue - 324022,
    fullRecordGapCenterValue - 324000,
    fullRecordGapCenterValue - 323938,
    fullRecordGapCenterValue - 323812,
    fullRecordGapCenterValue - 323754,
    fullRecordGapCenterValue - 323692,
    fullRecordGapCenterValue - 323644,
    fullRecordGapCenterValue - 323542,
    fullRecordGapCenterValue - 323538,
    fullRecordGapCenterValue - 323502,
    fullRecordGapCenterValue - 323482,
    fullRecordGapCenterValue - 323458,
    fullRecordGapCenterValue - 323452]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00026_fermat : ∀ n ∈ fullRecordGapRow00026_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01601_not_prime : ¬(recordGapCenter - 327982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327982]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01602_not_prime : ¬(recordGapCenter - 327802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327802]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01603_not_prime : ¬(recordGapCenter - 327724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327724]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01604_not_prime : ¬(recordGapCenter - 327718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327718]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01605_not_prime : ¬(recordGapCenter - 327498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327498]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01606_not_prime : ¬(recordGapCenter - 327462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327462]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01607_not_prime : ¬(recordGapCenter - 327394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327394]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01608_not_prime : ¬(recordGapCenter - 327388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327388]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01609_not_prime : ¬(recordGapCenter - 327358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327358]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01610_not_prime : ¬(recordGapCenter - 327322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327322]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01611_not_prime : ¬(recordGapCenter - 327282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327282]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01612_not_prime : ¬(recordGapCenter - 327274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327274]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01613_not_prime : ¬(recordGapCenter - 327018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327018]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01614_not_prime : ¬(recordGapCenter - 326994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326994]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01615_not_prime : ¬(recordGapCenter - 326812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326812]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01616_not_prime : ¬(recordGapCenter - 326734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326734]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01617_not_prime : ¬(recordGapCenter - 326694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326694]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01618_not_prime : ¬(recordGapCenter - 326514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326514]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01619_not_prime : ¬(recordGapCenter - 326478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326478]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01620_not_prime : ¬(recordGapCenter - 326422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326422]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01621_not_prime : ¬(recordGapCenter - 326338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326338]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01622_not_prime : ¬(recordGapCenter - 326254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326254]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01623_not_prime : ¬(recordGapCenter - 326212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326212]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01624_not_prime : ¬(recordGapCenter - 326202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326202]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01625_not_prime : ¬(recordGapCenter - 326122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326122]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01626_not_prime : ¬(recordGapCenter - 326038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 326038]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01627_not_prime : ¬(recordGapCenter - 325938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325938]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01628_not_prime : ¬(recordGapCenter - 325828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325828]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01629_not_prime : ¬(recordGapCenter - 325614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325614]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01630_not_prime : ¬(recordGapCenter - 325498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325498]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01631_not_prime : ¬(recordGapCenter - 325462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325462]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01632_not_prime : ¬(recordGapCenter - 325372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325372]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01633_not_prime : ¬(recordGapCenter - 325302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325302]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01634_not_prime : ¬(recordGapCenter - 325282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325282]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01635_not_prime : ¬(recordGapCenter - 325258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325258]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01636_not_prime : ¬(recordGapCenter - 325132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325132]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01637_not_prime : ¬(recordGapCenter - 325002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 325002]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01638_not_prime : ¬(recordGapCenter - 324798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324798]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01639_not_prime : ¬(recordGapCenter - 324778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324778]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01640_not_prime : ¬(recordGapCenter - 324718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324718]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01641_not_prime : ¬(recordGapCenter - 324652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324652]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01642_not_prime : ¬(recordGapCenter - 324628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324628]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01643_not_prime : ¬(recordGapCenter - 324538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324538]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01644_not_prime : ¬(recordGapCenter - 324498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324498]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01645_not_prime : ¬(recordGapCenter - 324442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324442]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01646_not_prime : ¬(recordGapCenter - 324354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324354]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01647_not_prime : ¬(recordGapCenter - 324238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324238]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01648_not_prime : ¬(recordGapCenter - 324172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324172]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01649_not_prime : ¬(recordGapCenter - 324118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324118]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01650_not_prime : ¬(recordGapCenter - 324078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324078]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01651_not_prime : ¬(recordGapCenter - 324034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324034]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01652_not_prime : ¬(recordGapCenter - 324022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324022]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01653_not_prime : ¬(recordGapCenter - 324000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 324000]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01654_not_prime : ¬(recordGapCenter - 323938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323938]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01655_not_prime : ¬(recordGapCenter - 323812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323812]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01656_not_prime : ¬(recordGapCenter - 323754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323754]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01657_not_prime : ¬(recordGapCenter - 323692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323692]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01658_not_prime : ¬(recordGapCenter - 323644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323644]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01659_not_prime : ¬(recordGapCenter - 323542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323542]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01660_not_prime : ¬(recordGapCenter - 323538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323538]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01661_not_prime : ¬(recordGapCenter - 323502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323502]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01662_not_prime : ¬(recordGapCenter - 323482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323482]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01663_not_prime : ¬(recordGapCenter - 323458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323458]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

theorem fullRecordGapTerm01664_not_prime : ¬(recordGapCenter - 323452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 323452]
  · apply fullRecordGapRow00026_fermat
    simp [fullRecordGapRow00026_values]

end PrimeFactorUnimodality
