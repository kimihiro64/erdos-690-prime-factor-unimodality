import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00050_values : List Nat :=
  [fullRecordGapCenterValue - 163054,
    fullRecordGapCenterValue - 162802,
    fullRecordGapCenterValue - 162742,
    fullRecordGapCenterValue - 162718,
    fullRecordGapCenterValue - 162154,
    fullRecordGapCenterValue - 162094,
    fullRecordGapCenterValue - 162000,
    fullRecordGapCenterValue - 161700,
    fullRecordGapCenterValue - 161698,
    fullRecordGapCenterValue - 161662,
    fullRecordGapCenterValue - 161362,
    fullRecordGapCenterValue - 161338,
    fullRecordGapCenterValue - 161280,
    fullRecordGapCenterValue - 160858,
    fullRecordGapCenterValue - 160774,
    fullRecordGapCenterValue - 160618,
    fullRecordGapCenterValue - 160078,
    fullRecordGapCenterValue - 159778,
    fullRecordGapCenterValue - 159694,
    fullRecordGapCenterValue - 159634,
    fullRecordGapCenterValue - 159382,
    fullRecordGapCenterValue - 158760,
    fullRecordGapCenterValue - 158674,
    fullRecordGapCenterValue - 158482,
    fullRecordGapCenterValue - 158400,
    fullRecordGapCenterValue - 158302,
    fullRecordGapCenterValue - 158062,
    fullRecordGapCenterValue - 157978,
    fullRecordGapCenterValue - 157714,
    fullRecordGapCenterValue - 157618,
    fullRecordGapCenterValue - 157594,
    fullRecordGapCenterValue - 157582,
    fullRecordGapCenterValue - 156874,
    fullRecordGapCenterValue - 156802,
    fullRecordGapCenterValue - 156694,
    fullRecordGapCenterValue - 156382,
    fullRecordGapCenterValue - 156250,
    fullRecordGapCenterValue - 156082,
    fullRecordGapCenterValue - 155998,
    fullRecordGapCenterValue - 155902,
    fullRecordGapCenterValue - 155734,
    fullRecordGapCenterValue - 155602,
    fullRecordGapCenterValue - 155398,
    fullRecordGapCenterValue - 155362,
    fullRecordGapCenterValue - 155232,
    fullRecordGapCenterValue - 154702,
    fullRecordGapCenterValue - 154558,
    fullRecordGapCenterValue - 154342,
    fullRecordGapCenterValue - 154282,
    fullRecordGapCenterValue - 154138,
    fullRecordGapCenterValue - 153922,
    fullRecordGapCenterValue - 153838,
    fullRecordGapCenterValue - 153664,
    fullRecordGapCenterValue - 153600,
    fullRecordGapCenterValue - 153562,
    fullRecordGapCenterValue - 153514,
    fullRecordGapCenterValue - 153358,
    fullRecordGapCenterValue - 153262,
    fullRecordGapCenterValue - 153214,
    fullRecordGapCenterValue - 152962,
    fullRecordGapCenterValue - 152842,
    fullRecordGapCenterValue - 152758,
    fullRecordGapCenterValue - 152158,
    fullRecordGapCenterValue - 152064]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00050_fermat : ∀ n ∈ fullRecordGapRow00050_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03137_not_prime : ¬(recordGapCenter - 163054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163054]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03138_not_prime : ¬(recordGapCenter - 162802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 162802]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03139_not_prime : ¬(recordGapCenter - 162742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 162742]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03140_not_prime : ¬(recordGapCenter - 162718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 162718]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03141_not_prime : ¬(recordGapCenter - 162154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 162154]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03142_not_prime : ¬(recordGapCenter - 162094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 162094]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03143_not_prime : ¬(recordGapCenter - 162000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 162000]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03144_not_prime : ¬(recordGapCenter - 161700).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 161700]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03145_not_prime : ¬(recordGapCenter - 161698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 161698]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03146_not_prime : ¬(recordGapCenter - 161662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 161662]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03147_not_prime : ¬(recordGapCenter - 161362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 161362]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03148_not_prime : ¬(recordGapCenter - 161338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 161338]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03149_not_prime : ¬(recordGapCenter - 161280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 161280]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03150_not_prime : ¬(recordGapCenter - 160858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 160858]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03151_not_prime : ¬(recordGapCenter - 160774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 160774]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03152_not_prime : ¬(recordGapCenter - 160618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 160618]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03153_not_prime : ¬(recordGapCenter - 160078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 160078]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03154_not_prime : ¬(recordGapCenter - 159778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 159778]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03155_not_prime : ¬(recordGapCenter - 159694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 159694]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03156_not_prime : ¬(recordGapCenter - 159634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 159634]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03157_not_prime : ¬(recordGapCenter - 159382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 159382]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03158_not_prime : ¬(recordGapCenter - 158760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 158760]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03159_not_prime : ¬(recordGapCenter - 158674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 158674]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03160_not_prime : ¬(recordGapCenter - 158482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 158482]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03161_not_prime : ¬(recordGapCenter - 158400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 158400]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03162_not_prime : ¬(recordGapCenter - 158302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 158302]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03163_not_prime : ¬(recordGapCenter - 158062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 158062]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03164_not_prime : ¬(recordGapCenter - 157978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 157978]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03165_not_prime : ¬(recordGapCenter - 157714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 157714]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03166_not_prime : ¬(recordGapCenter - 157618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 157618]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03167_not_prime : ¬(recordGapCenter - 157594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 157594]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03168_not_prime : ¬(recordGapCenter - 157582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 157582]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03169_not_prime : ¬(recordGapCenter - 156874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 156874]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03170_not_prime : ¬(recordGapCenter - 156802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 156802]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03171_not_prime : ¬(recordGapCenter - 156694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 156694]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03172_not_prime : ¬(recordGapCenter - 156382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 156382]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03173_not_prime : ¬(recordGapCenter - 156250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 156250]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03174_not_prime : ¬(recordGapCenter - 156082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 156082]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03175_not_prime : ¬(recordGapCenter - 155998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 155998]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03176_not_prime : ¬(recordGapCenter - 155902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 155902]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03177_not_prime : ¬(recordGapCenter - 155734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 155734]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03178_not_prime : ¬(recordGapCenter - 155602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 155602]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03179_not_prime : ¬(recordGapCenter - 155398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 155398]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03180_not_prime : ¬(recordGapCenter - 155362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 155362]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03181_not_prime : ¬(recordGapCenter - 155232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 155232]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03182_not_prime : ¬(recordGapCenter - 154702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 154702]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03183_not_prime : ¬(recordGapCenter - 154558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 154558]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03184_not_prime : ¬(recordGapCenter - 154342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 154342]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03185_not_prime : ¬(recordGapCenter - 154282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 154282]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03186_not_prime : ¬(recordGapCenter - 154138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 154138]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03187_not_prime : ¬(recordGapCenter - 153922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153922]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03188_not_prime : ¬(recordGapCenter - 153838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153838]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03189_not_prime : ¬(recordGapCenter - 153664).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153664]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03190_not_prime : ¬(recordGapCenter - 153600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153600]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03191_not_prime : ¬(recordGapCenter - 153562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153562]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03192_not_prime : ¬(recordGapCenter - 153514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153514]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03193_not_prime : ¬(recordGapCenter - 153358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153358]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03194_not_prime : ¬(recordGapCenter - 153262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153262]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03195_not_prime : ¬(recordGapCenter - 153214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 153214]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03196_not_prime : ¬(recordGapCenter - 152962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 152962]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03197_not_prime : ¬(recordGapCenter - 152842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 152842]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03198_not_prime : ¬(recordGapCenter - 152758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 152758]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03199_not_prime : ¬(recordGapCenter - 152158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 152158]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

theorem fullRecordGapTerm03200_not_prime : ¬(recordGapCenter - 152064).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 152064]
  · apply fullRecordGapRow00050_fermat
    simp [fullRecordGapRow00050_values]

end PrimeFactorUnimodality
