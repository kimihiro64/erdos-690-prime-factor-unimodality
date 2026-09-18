import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00032_values : List Nat :=
  [fullRecordGapCenterValue - 293842,
    fullRecordGapCenterValue - 293838,
    fullRecordGapCenterValue - 293718,
    fullRecordGapCenterValue - 293668,
    fullRecordGapCenterValue - 293614,
    fullRecordGapCenterValue - 293452,
    fullRecordGapCenterValue - 293334,
    fullRecordGapCenterValue - 293298,
    fullRecordGapCenterValue - 293278,
    fullRecordGapCenterValue - 293218,
    fullRecordGapCenterValue - 293214,
    fullRecordGapCenterValue - 292542,
    fullRecordGapCenterValue - 292282,
    fullRecordGapCenterValue - 292074,
    fullRecordGapCenterValue - 292018,
    fullRecordGapCenterValue - 291748,
    fullRecordGapCenterValue - 291738,
    fullRecordGapCenterValue - 291598,
    fullRecordGapCenterValue - 291358,
    fullRecordGapCenterValue - 291322,
    fullRecordGapCenterValue - 291274,
    fullRecordGapCenterValue - 291268,
    fullRecordGapCenterValue - 291234,
    fullRecordGapCenterValue - 291202,
    fullRecordGapCenterValue - 291198,
    fullRecordGapCenterValue - 291178,
    fullRecordGapCenterValue - 291154,
    fullRecordGapCenterValue - 291052,
    fullRecordGapCenterValue - 291022,
    fullRecordGapCenterValue - 290922,
    fullRecordGapCenterValue - 290908,
    fullRecordGapCenterValue - 290694,
    fullRecordGapCenterValue - 290622,
    fullRecordGapCenterValue - 290614,
    fullRecordGapCenterValue - 290572,
    fullRecordGapCenterValue - 290518,
    fullRecordGapCenterValue - 290478,
    fullRecordGapCenterValue - 290454,
    fullRecordGapCenterValue - 290442,
    fullRecordGapCenterValue - 290400,
    fullRecordGapCenterValue - 290304,
    fullRecordGapCenterValue - 290218,
    fullRecordGapCenterValue - 290182,
    fullRecordGapCenterValue - 290062,
    fullRecordGapCenterValue - 289972,
    fullRecordGapCenterValue - 289834,
    fullRecordGapCenterValue - 289798,
    fullRecordGapCenterValue - 289684,
    fullRecordGapCenterValue - 289582,
    fullRecordGapCenterValue - 289558,
    fullRecordGapCenterValue - 289554,
    fullRecordGapCenterValue - 289482,
    fullRecordGapCenterValue - 289468,
    fullRecordGapCenterValue - 289462,
    fullRecordGapCenterValue - 289438,
    fullRecordGapCenterValue - 289434,
    fullRecordGapCenterValue - 289342,
    fullRecordGapCenterValue - 289252,
    fullRecordGapCenterValue - 289228,
    fullRecordGapCenterValue - 289222,
    fullRecordGapCenterValue - 289182,
    fullRecordGapCenterValue - 289158,
    fullRecordGapCenterValue - 289074,
    fullRecordGapCenterValue - 289012]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00032_fermat : ∀ n ∈ fullRecordGapRow00032_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01985_not_prime : ¬(recordGapCenter - 293842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293842]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm01986_not_prime : ¬(recordGapCenter - 293838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293838]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm01987_not_prime : ¬(recordGapCenter - 293718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293718]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm01988_not_prime : ¬(recordGapCenter - 293668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293668]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm01989_not_prime : ¬(recordGapCenter - 293614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293614]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm01990_not_prime : ¬(recordGapCenter - 293452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293452]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm01991_not_prime : ¬(recordGapCenter - 293334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293334]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm01992_not_prime : ¬(recordGapCenter - 293298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293298]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm01993_not_prime : ¬(recordGapCenter - 293278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293278]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm01994_not_prime : ¬(recordGapCenter - 293218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293218]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm01995_not_prime : ¬(recordGapCenter - 293214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 293214]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm01996_not_prime : ¬(recordGapCenter - 292542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 292542]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm01997_not_prime : ¬(recordGapCenter - 292282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 292282]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm01998_not_prime : ¬(recordGapCenter - 292074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 292074]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm01999_not_prime : ¬(recordGapCenter - 292018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 292018]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02000_not_prime : ¬(recordGapCenter - 291748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291748]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02001_not_prime : ¬(recordGapCenter - 291738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291738]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02002_not_prime : ¬(recordGapCenter - 291598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291598]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02003_not_prime : ¬(recordGapCenter - 291358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291358]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02004_not_prime : ¬(recordGapCenter - 291322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291322]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02005_not_prime : ¬(recordGapCenter - 291274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291274]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02006_not_prime : ¬(recordGapCenter - 291268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291268]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02007_not_prime : ¬(recordGapCenter - 291234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291234]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02008_not_prime : ¬(recordGapCenter - 291202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291202]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02009_not_prime : ¬(recordGapCenter - 291198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291198]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02010_not_prime : ¬(recordGapCenter - 291178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291178]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02011_not_prime : ¬(recordGapCenter - 291154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291154]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02012_not_prime : ¬(recordGapCenter - 291052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291052]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02013_not_prime : ¬(recordGapCenter - 291022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 291022]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02014_not_prime : ¬(recordGapCenter - 290922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290922]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02015_not_prime : ¬(recordGapCenter - 290908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290908]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02016_not_prime : ¬(recordGapCenter - 290694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290694]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02017_not_prime : ¬(recordGapCenter - 290622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290622]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02018_not_prime : ¬(recordGapCenter - 290614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290614]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02019_not_prime : ¬(recordGapCenter - 290572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290572]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02020_not_prime : ¬(recordGapCenter - 290518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290518]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02021_not_prime : ¬(recordGapCenter - 290478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290478]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02022_not_prime : ¬(recordGapCenter - 290454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290454]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02023_not_prime : ¬(recordGapCenter - 290442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290442]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02024_not_prime : ¬(recordGapCenter - 290400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290400]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02025_not_prime : ¬(recordGapCenter - 290304).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290304]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02026_not_prime : ¬(recordGapCenter - 290218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290218]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02027_not_prime : ¬(recordGapCenter - 290182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290182]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02028_not_prime : ¬(recordGapCenter - 290062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 290062]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02029_not_prime : ¬(recordGapCenter - 289972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289972]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02030_not_prime : ¬(recordGapCenter - 289834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289834]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02031_not_prime : ¬(recordGapCenter - 289798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289798]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02032_not_prime : ¬(recordGapCenter - 289684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289684]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02033_not_prime : ¬(recordGapCenter - 289582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289582]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02034_not_prime : ¬(recordGapCenter - 289558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289558]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02035_not_prime : ¬(recordGapCenter - 289554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289554]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02036_not_prime : ¬(recordGapCenter - 289482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289482]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02037_not_prime : ¬(recordGapCenter - 289468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289468]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02038_not_prime : ¬(recordGapCenter - 289462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289462]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02039_not_prime : ¬(recordGapCenter - 289438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289438]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02040_not_prime : ¬(recordGapCenter - 289434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289434]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02041_not_prime : ¬(recordGapCenter - 289342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289342]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02042_not_prime : ¬(recordGapCenter - 289252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289252]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02043_not_prime : ¬(recordGapCenter - 289228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289228]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02044_not_prime : ¬(recordGapCenter - 289222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289222]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02045_not_prime : ¬(recordGapCenter - 289182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289182]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02046_not_prime : ¬(recordGapCenter - 289158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289158]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02047_not_prime : ¬(recordGapCenter - 289074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289074]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm02048_not_prime : ¬(recordGapCenter - 289012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 289012]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

end PrimeFactorUnimodality
