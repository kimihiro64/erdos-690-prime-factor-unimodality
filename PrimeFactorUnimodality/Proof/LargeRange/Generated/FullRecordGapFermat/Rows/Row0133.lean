import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00133_values : List Nat :=
  [fullRecordGapCenterValue + 502616,
    fullRecordGapCenterValue + 502638,
    fullRecordGapCenterValue + 502730,
    fullRecordGapCenterValue + 502772,
    fullRecordGapCenterValue + 502910,
    fullRecordGapCenterValue + 502946,
    fullRecordGapCenterValue + 503066,
    fullRecordGapCenterValue + 503156,
    fullRecordGapCenterValue + 503252,
    fullRecordGapCenterValue + 503330,
    fullRecordGapCenterValue + 503402,
    fullRecordGapCenterValue + 503522,
    fullRecordGapCenterValue + 503582,
    fullRecordGapCenterValue + 503618,
    fullRecordGapCenterValue + 503732,
    fullRecordGapCenterValue + 503870,
    fullRecordGapCenterValue + 503912,
    fullRecordGapCenterValue + 504000,
    fullRecordGapCenterValue + 504002,
    fullRecordGapCenterValue + 504026,
    fullRecordGapCenterValue + 504210,
    fullRecordGapCenterValue + 504318,
    fullRecordGapCenterValue + 504326,
    fullRecordGapCenterValue + 504338,
    fullRecordGapCenterValue + 504362,
    fullRecordGapCenterValue + 504386,
    fullRecordGapCenterValue + 504402,
    fullRecordGapCenterValue + 504726,
    fullRecordGapCenterValue + 504782,
    fullRecordGapCenterValue + 504908,
    fullRecordGapCenterValue + 504932,
    fullRecordGapCenterValue + 504978,
    fullRecordGapCenterValue + 505016,
    fullRecordGapCenterValue + 505082,
    fullRecordGapCenterValue + 505086,
    fullRecordGapCenterValue + 505130,
    fullRecordGapCenterValue + 505166,
    fullRecordGapCenterValue + 505178,
    fullRecordGapCenterValue + 505418,
    fullRecordGapCenterValue + 505482,
    fullRecordGapCenterValue + 505646,
    fullRecordGapCenterValue + 505772,
    fullRecordGapCenterValue + 505838,
    fullRecordGapCenterValue + 505902,
    fullRecordGapCenterValue + 505928,
    fullRecordGapCenterValue + 505958,
    fullRecordGapCenterValue + 505976,
    fullRecordGapCenterValue + 506082,
    fullRecordGapCenterValue + 506126,
    fullRecordGapCenterValue + 506250,
    fullRecordGapCenterValue + 506270,
    fullRecordGapCenterValue + 506318,
    fullRecordGapCenterValue + 506406,
    fullRecordGapCenterValue + 506510,
    fullRecordGapCenterValue + 506642,
    fullRecordGapCenterValue + 506658,
    fullRecordGapCenterValue + 506696,
    fullRecordGapCenterValue + 506732,
    fullRecordGapCenterValue + 506742,
    fullRecordGapCenterValue + 506762,
    fullRecordGapCenterValue + 506852,
    fullRecordGapCenterValue + 506936,
    fullRecordGapCenterValue + 507146,
    fullRecordGapCenterValue + 507218]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00133_fermat : ∀ n ∈ fullRecordGapRow00133_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08449_not_prime : ¬(recordGapCenter + 502616).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502616]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08450_not_prime : ¬(recordGapCenter + 502638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502638]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08451_not_prime : ¬(recordGapCenter + 502730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502730]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08452_not_prime : ¬(recordGapCenter + 502772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502772]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08453_not_prime : ¬(recordGapCenter + 502910).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502910]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08454_not_prime : ¬(recordGapCenter + 502946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 502946]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08455_not_prime : ¬(recordGapCenter + 503066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 503066]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08456_not_prime : ¬(recordGapCenter + 503156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 503156]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08457_not_prime : ¬(recordGapCenter + 503252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 503252]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08458_not_prime : ¬(recordGapCenter + 503330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 503330]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08459_not_prime : ¬(recordGapCenter + 503402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 503402]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08460_not_prime : ¬(recordGapCenter + 503522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 503522]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08461_not_prime : ¬(recordGapCenter + 503582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 503582]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08462_not_prime : ¬(recordGapCenter + 503618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 503618]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08463_not_prime : ¬(recordGapCenter + 503732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 503732]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08464_not_prime : ¬(recordGapCenter + 503870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 503870]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08465_not_prime : ¬(recordGapCenter + 503912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 503912]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08466_not_prime : ¬(recordGapCenter + 504000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504000]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08467_not_prime : ¬(recordGapCenter + 504002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504002]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08468_not_prime : ¬(recordGapCenter + 504026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504026]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08469_not_prime : ¬(recordGapCenter + 504210).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504210]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08470_not_prime : ¬(recordGapCenter + 504318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504318]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08471_not_prime : ¬(recordGapCenter + 504326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504326]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08472_not_prime : ¬(recordGapCenter + 504338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504338]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08473_not_prime : ¬(recordGapCenter + 504362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504362]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08474_not_prime : ¬(recordGapCenter + 504386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504386]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08475_not_prime : ¬(recordGapCenter + 504402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504402]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08476_not_prime : ¬(recordGapCenter + 504726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504726]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08477_not_prime : ¬(recordGapCenter + 504782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504782]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08478_not_prime : ¬(recordGapCenter + 504908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504908]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08479_not_prime : ¬(recordGapCenter + 504932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504932]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08480_not_prime : ¬(recordGapCenter + 504978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 504978]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08481_not_prime : ¬(recordGapCenter + 505016).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505016]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08482_not_prime : ¬(recordGapCenter + 505082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505082]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08483_not_prime : ¬(recordGapCenter + 505086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505086]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08484_not_prime : ¬(recordGapCenter + 505130).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505130]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08485_not_prime : ¬(recordGapCenter + 505166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505166]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08486_not_prime : ¬(recordGapCenter + 505178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505178]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08487_not_prime : ¬(recordGapCenter + 505418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505418]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08488_not_prime : ¬(recordGapCenter + 505482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505482]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08489_not_prime : ¬(recordGapCenter + 505646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505646]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08490_not_prime : ¬(recordGapCenter + 505772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505772]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08491_not_prime : ¬(recordGapCenter + 505838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505838]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08492_not_prime : ¬(recordGapCenter + 505902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505902]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08493_not_prime : ¬(recordGapCenter + 505928).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505928]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08494_not_prime : ¬(recordGapCenter + 505958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505958]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08495_not_prime : ¬(recordGapCenter + 505976).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 505976]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08496_not_prime : ¬(recordGapCenter + 506082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506082]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08497_not_prime : ¬(recordGapCenter + 506126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506126]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08498_not_prime : ¬(recordGapCenter + 506250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506250]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08499_not_prime : ¬(recordGapCenter + 506270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506270]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08500_not_prime : ¬(recordGapCenter + 506318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506318]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08501_not_prime : ¬(recordGapCenter + 506406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506406]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08502_not_prime : ¬(recordGapCenter + 506510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506510]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08503_not_prime : ¬(recordGapCenter + 506642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506642]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08504_not_prime : ¬(recordGapCenter + 506658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506658]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08505_not_prime : ¬(recordGapCenter + 506696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506696]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08506_not_prime : ¬(recordGapCenter + 506732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506732]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08507_not_prime : ¬(recordGapCenter + 506742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506742]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08508_not_prime : ¬(recordGapCenter + 506762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506762]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08509_not_prime : ¬(recordGapCenter + 506852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506852]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08510_not_prime : ¬(recordGapCenter + 506936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 506936]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08511_not_prime : ¬(recordGapCenter + 507146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507146]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

theorem fullRecordGapTerm08512_not_prime : ¬(recordGapCenter + 507218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 507218]
  · apply fullRecordGapRow00133_fermat
    simp [fullRecordGapRow00133_values]

end PrimeFactorUnimodality
