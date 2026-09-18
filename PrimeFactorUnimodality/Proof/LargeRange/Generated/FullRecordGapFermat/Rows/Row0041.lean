import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00041_values : List Nat :=
  [fullRecordGapCenterValue - 236122,
    fullRecordGapCenterValue - 236092,
    fullRecordGapCenterValue - 236044,
    fullRecordGapCenterValue - 235918,
    fullRecordGapCenterValue - 235678,
    fullRecordGapCenterValue - 235618,
    fullRecordGapCenterValue - 235594,
    fullRecordGapCenterValue - 235402,
    fullRecordGapCenterValue - 235200,
    fullRecordGapCenterValue - 234862,
    fullRecordGapCenterValue - 234772,
    fullRecordGapCenterValue - 234748,
    fullRecordGapCenterValue - 234742,
    fullRecordGapCenterValue - 234538,
    fullRecordGapCenterValue - 234478,
    fullRecordGapCenterValue - 234418,
    fullRecordGapCenterValue - 234202,
    fullRecordGapCenterValue - 234148,
    fullRecordGapCenterValue - 233698,
    fullRecordGapCenterValue - 233638,
    fullRecordGapCenterValue - 233572,
    fullRecordGapCenterValue - 233452,
    fullRecordGapCenterValue - 233284,
    fullRecordGapCenterValue - 233074,
    fullRecordGapCenterValue - 233062,
    fullRecordGapCenterValue - 232822,
    fullRecordGapCenterValue - 232612,
    fullRecordGapCenterValue - 232444,
    fullRecordGapCenterValue - 232402,
    fullRecordGapCenterValue - 232378,
    fullRecordGapCenterValue - 232320,
    fullRecordGapCenterValue - 232054,
    fullRecordGapCenterValue - 231964,
    fullRecordGapCenterValue - 231892,
    fullRecordGapCenterValue - 231802,
    fullRecordGapCenterValue - 231772,
    fullRecordGapCenterValue - 231754,
    fullRecordGapCenterValue - 231718,
    fullRecordGapCenterValue - 231622,
    fullRecordGapCenterValue - 231604,
    fullRecordGapCenterValue - 231562,
    fullRecordGapCenterValue - 231454,
    fullRecordGapCenterValue - 231412,
    fullRecordGapCenterValue - 231388,
    fullRecordGapCenterValue - 231178,
    fullRecordGapCenterValue - 231172,
    fullRecordGapCenterValue - 231142,
    fullRecordGapCenterValue - 231094,
    fullRecordGapCenterValue - 230638,
    fullRecordGapCenterValue - 230302,
    fullRecordGapCenterValue - 230134,
    fullRecordGapCenterValue - 229654,
    fullRecordGapCenterValue - 229324,
    fullRecordGapCenterValue - 229198,
    fullRecordGapCenterValue - 228934,
    fullRecordGapCenterValue - 228690,
    fullRecordGapCenterValue - 228658,
    fullRecordGapCenterValue - 228622,
    fullRecordGapCenterValue - 228598,
    fullRecordGapCenterValue - 228442,
    fullRecordGapCenterValue - 228388,
    fullRecordGapCenterValue - 228322,
    fullRecordGapCenterValue - 227938,
    fullRecordGapCenterValue - 227782]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00041_fermat : ∀ n ∈ fullRecordGapRow00041_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02561_not_prime : ¬(recordGapCenter - 236122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236122]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02562_not_prime : ¬(recordGapCenter - 236092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236092]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02563_not_prime : ¬(recordGapCenter - 236044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236044]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02564_not_prime : ¬(recordGapCenter - 235918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 235918]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02565_not_prime : ¬(recordGapCenter - 235678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 235678]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02566_not_prime : ¬(recordGapCenter - 235618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 235618]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02567_not_prime : ¬(recordGapCenter - 235594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 235594]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02568_not_prime : ¬(recordGapCenter - 235402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 235402]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02569_not_prime : ¬(recordGapCenter - 235200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 235200]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02570_not_prime : ¬(recordGapCenter - 234862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234862]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02571_not_prime : ¬(recordGapCenter - 234772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234772]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02572_not_prime : ¬(recordGapCenter - 234748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234748]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02573_not_prime : ¬(recordGapCenter - 234742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234742]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02574_not_prime : ¬(recordGapCenter - 234538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234538]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02575_not_prime : ¬(recordGapCenter - 234478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234478]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02576_not_prime : ¬(recordGapCenter - 234418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234418]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02577_not_prime : ¬(recordGapCenter - 234202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234202]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02578_not_prime : ¬(recordGapCenter - 234148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234148]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02579_not_prime : ¬(recordGapCenter - 233698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 233698]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02580_not_prime : ¬(recordGapCenter - 233638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 233638]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02581_not_prime : ¬(recordGapCenter - 233572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 233572]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02582_not_prime : ¬(recordGapCenter - 233452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 233452]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02583_not_prime : ¬(recordGapCenter - 233284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 233284]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02584_not_prime : ¬(recordGapCenter - 233074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 233074]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02585_not_prime : ¬(recordGapCenter - 233062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 233062]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02586_not_prime : ¬(recordGapCenter - 232822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 232822]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02587_not_prime : ¬(recordGapCenter - 232612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 232612]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02588_not_prime : ¬(recordGapCenter - 232444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 232444]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02589_not_prime : ¬(recordGapCenter - 232402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 232402]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02590_not_prime : ¬(recordGapCenter - 232378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 232378]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02591_not_prime : ¬(recordGapCenter - 232320).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 232320]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02592_not_prime : ¬(recordGapCenter - 232054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 232054]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02593_not_prime : ¬(recordGapCenter - 231964).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231964]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02594_not_prime : ¬(recordGapCenter - 231892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231892]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02595_not_prime : ¬(recordGapCenter - 231802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231802]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02596_not_prime : ¬(recordGapCenter - 231772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231772]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02597_not_prime : ¬(recordGapCenter - 231754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231754]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02598_not_prime : ¬(recordGapCenter - 231718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231718]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02599_not_prime : ¬(recordGapCenter - 231622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231622]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02600_not_prime : ¬(recordGapCenter - 231604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231604]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02601_not_prime : ¬(recordGapCenter - 231562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231562]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02602_not_prime : ¬(recordGapCenter - 231454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231454]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02603_not_prime : ¬(recordGapCenter - 231412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231412]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02604_not_prime : ¬(recordGapCenter - 231388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231388]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02605_not_prime : ¬(recordGapCenter - 231178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231178]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02606_not_prime : ¬(recordGapCenter - 231172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231172]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02607_not_prime : ¬(recordGapCenter - 231142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231142]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02608_not_prime : ¬(recordGapCenter - 231094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231094]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02609_not_prime : ¬(recordGapCenter - 230638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 230638]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02610_not_prime : ¬(recordGapCenter - 230302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 230302]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02611_not_prime : ¬(recordGapCenter - 230134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 230134]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02612_not_prime : ¬(recordGapCenter - 229654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 229654]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02613_not_prime : ¬(recordGapCenter - 229324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 229324]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02614_not_prime : ¬(recordGapCenter - 229198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 229198]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02615_not_prime : ¬(recordGapCenter - 228934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228934]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02616_not_prime : ¬(recordGapCenter - 228690).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228690]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02617_not_prime : ¬(recordGapCenter - 228658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228658]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02618_not_prime : ¬(recordGapCenter - 228622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228622]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02619_not_prime : ¬(recordGapCenter - 228598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228598]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02620_not_prime : ¬(recordGapCenter - 228442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228442]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02621_not_prime : ¬(recordGapCenter - 228388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228388]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02622_not_prime : ¬(recordGapCenter - 228322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228322]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02623_not_prime : ¬(recordGapCenter - 227938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227938]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

theorem fullRecordGapTerm02624_not_prime : ¬(recordGapCenter - 227782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227782]
  · apply fullRecordGapRow00041_fermat
    simp [fullRecordGapRow00041_values]

end PrimeFactorUnimodality
