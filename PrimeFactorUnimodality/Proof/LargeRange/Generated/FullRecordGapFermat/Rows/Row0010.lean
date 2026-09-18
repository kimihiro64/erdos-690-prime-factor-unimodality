import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00010_values : List Nat :=
  [fullRecordGapCenterValue - 409948,
    fullRecordGapCenterValue - 409924,
    fullRecordGapCenterValue - 409894,
    fullRecordGapCenterValue - 409804,
    fullRecordGapCenterValue - 409624,
    fullRecordGapCenterValue - 409588,
    fullRecordGapCenterValue - 409582,
    fullRecordGapCenterValue - 409434,
    fullRecordGapCenterValue - 409348,
    fullRecordGapCenterValue - 409282,
    fullRecordGapCenterValue - 409198,
    fullRecordGapCenterValue - 409114,
    fullRecordGapCenterValue - 409042,
    fullRecordGapCenterValue - 409012,
    fullRecordGapCenterValue - 408922,
    fullRecordGapCenterValue - 408868,
    fullRecordGapCenterValue - 408862,
    fullRecordGapCenterValue - 408718,
    fullRecordGapCenterValue - 408678,
    fullRecordGapCenterValue - 408622,
    fullRecordGapCenterValue - 408568,
    fullRecordGapCenterValue - 408484,
    fullRecordGapCenterValue - 408354,
    fullRecordGapCenterValue - 408322,
    fullRecordGapCenterValue - 408274,
    fullRecordGapCenterValue - 408244,
    fullRecordGapCenterValue - 408240,
    fullRecordGapCenterValue - 408202,
    fullRecordGapCenterValue - 408124,
    fullRecordGapCenterValue - 408118,
    fullRecordGapCenterValue - 407998,
    fullRecordGapCenterValue - 407958,
    fullRecordGapCenterValue - 407938,
    fullRecordGapCenterValue - 407908,
    fullRecordGapCenterValue - 407634,
    fullRecordGapCenterValue - 407614,
    fullRecordGapCenterValue - 407578,
    fullRecordGapCenterValue - 407188,
    fullRecordGapCenterValue - 407182,
    fullRecordGapCenterValue - 406948,
    fullRecordGapCenterValue - 406774,
    fullRecordGapCenterValue - 406702,
    fullRecordGapCenterValue - 406444,
    fullRecordGapCenterValue - 406282,
    fullRecordGapCenterValue - 406114,
    fullRecordGapCenterValue - 406108,
    fullRecordGapCenterValue - 406024,
    fullRecordGapCenterValue - 405934,
    fullRecordGapCenterValue - 405814,
    fullRecordGapCenterValue - 405778,
    fullRecordGapCenterValue - 405718,
    fullRecordGapCenterValue - 405642,
    fullRecordGapCenterValue - 405534,
    fullRecordGapCenterValue - 405514,
    fullRecordGapCenterValue - 405402,
    fullRecordGapCenterValue - 405388,
    fullRecordGapCenterValue - 405148,
    fullRecordGapCenterValue - 405138,
    fullRecordGapCenterValue - 405124,
    fullRecordGapCenterValue - 404962,
    fullRecordGapCenterValue - 404812,
    fullRecordGapCenterValue - 404788,
    fullRecordGapCenterValue - 404728,
    fullRecordGapCenterValue - 404682]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00010_fermat : ∀ n ∈ fullRecordGapRow00010_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00577_not_prime : ¬(recordGapCenter - 409948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409948]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00578_not_prime : ¬(recordGapCenter - 409924).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409924]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00579_not_prime : ¬(recordGapCenter - 409894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409894]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00580_not_prime : ¬(recordGapCenter - 409804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409804]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00581_not_prime : ¬(recordGapCenter - 409624).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409624]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00582_not_prime : ¬(recordGapCenter - 409588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409588]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00583_not_prime : ¬(recordGapCenter - 409582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409582]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00584_not_prime : ¬(recordGapCenter - 409434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409434]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00585_not_prime : ¬(recordGapCenter - 409348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409348]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00586_not_prime : ¬(recordGapCenter - 409282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409282]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00587_not_prime : ¬(recordGapCenter - 409198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409198]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00588_not_prime : ¬(recordGapCenter - 409114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409114]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00589_not_prime : ¬(recordGapCenter - 409042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409042]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00590_not_prime : ¬(recordGapCenter - 409012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 409012]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00591_not_prime : ¬(recordGapCenter - 408922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408922]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00592_not_prime : ¬(recordGapCenter - 408868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408868]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00593_not_prime : ¬(recordGapCenter - 408862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408862]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00594_not_prime : ¬(recordGapCenter - 408718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408718]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00595_not_prime : ¬(recordGapCenter - 408678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408678]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00596_not_prime : ¬(recordGapCenter - 408622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408622]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00597_not_prime : ¬(recordGapCenter - 408568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408568]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00598_not_prime : ¬(recordGapCenter - 408484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408484]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00599_not_prime : ¬(recordGapCenter - 408354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408354]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00600_not_prime : ¬(recordGapCenter - 408322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408322]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00601_not_prime : ¬(recordGapCenter - 408274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408274]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00602_not_prime : ¬(recordGapCenter - 408244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408244]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00603_not_prime : ¬(recordGapCenter - 408240).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408240]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00604_not_prime : ¬(recordGapCenter - 408202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408202]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00605_not_prime : ¬(recordGapCenter - 408124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408124]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00606_not_prime : ¬(recordGapCenter - 408118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 408118]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00607_not_prime : ¬(recordGapCenter - 407998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407998]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00608_not_prime : ¬(recordGapCenter - 407958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407958]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00609_not_prime : ¬(recordGapCenter - 407938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407938]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00610_not_prime : ¬(recordGapCenter - 407908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407908]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00611_not_prime : ¬(recordGapCenter - 407634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407634]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00612_not_prime : ¬(recordGapCenter - 407614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407614]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00613_not_prime : ¬(recordGapCenter - 407578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407578]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00614_not_prime : ¬(recordGapCenter - 407188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407188]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00615_not_prime : ¬(recordGapCenter - 407182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 407182]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00616_not_prime : ¬(recordGapCenter - 406948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406948]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00617_not_prime : ¬(recordGapCenter - 406774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406774]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00618_not_prime : ¬(recordGapCenter - 406702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406702]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00619_not_prime : ¬(recordGapCenter - 406444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406444]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00620_not_prime : ¬(recordGapCenter - 406282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406282]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00621_not_prime : ¬(recordGapCenter - 406114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406114]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00622_not_prime : ¬(recordGapCenter - 406108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406108]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00623_not_prime : ¬(recordGapCenter - 406024).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 406024]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00624_not_prime : ¬(recordGapCenter - 405934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405934]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00625_not_prime : ¬(recordGapCenter - 405814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405814]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00626_not_prime : ¬(recordGapCenter - 405778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405778]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00627_not_prime : ¬(recordGapCenter - 405718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405718]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00628_not_prime : ¬(recordGapCenter - 405642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405642]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00629_not_prime : ¬(recordGapCenter - 405534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405534]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00630_not_prime : ¬(recordGapCenter - 405514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405514]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00631_not_prime : ¬(recordGapCenter - 405402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405402]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00632_not_prime : ¬(recordGapCenter - 405388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405388]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00633_not_prime : ¬(recordGapCenter - 405148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405148]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00634_not_prime : ¬(recordGapCenter - 405138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405138]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00635_not_prime : ¬(recordGapCenter - 405124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 405124]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00636_not_prime : ¬(recordGapCenter - 404962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404962]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00637_not_prime : ¬(recordGapCenter - 404812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404812]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00638_not_prime : ¬(recordGapCenter - 404788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404788]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00639_not_prime : ¬(recordGapCenter - 404728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404728]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm00640_not_prime : ¬(recordGapCenter - 404682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 404682]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

end PrimeFactorUnimodality
