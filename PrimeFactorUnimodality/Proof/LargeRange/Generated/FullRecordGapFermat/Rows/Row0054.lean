import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00054_values : List Nat :=
  [fullRecordGapCenterValue - 117358,
    fullRecordGapCenterValue - 116962,
    fullRecordGapCenterValue - 116902,
    fullRecordGapCenterValue - 116878,
    fullRecordGapCenterValue - 116458,
    fullRecordGapCenterValue - 116424,
    fullRecordGapCenterValue - 116422,
    fullRecordGapCenterValue - 116134,
    fullRecordGapCenterValue - 115762,
    fullRecordGapCenterValue - 115500,
    fullRecordGapCenterValue - 115114,
    fullRecordGapCenterValue - 115054,
    fullRecordGapCenterValue - 114694,
    fullRecordGapCenterValue - 114658,
    fullRecordGapCenterValue - 114502,
    fullRecordGapCenterValue - 114442,
    fullRecordGapCenterValue - 114298,
    fullRecordGapCenterValue - 113914,
    fullRecordGapCenterValue - 113902,
    fullRecordGapCenterValue - 113794,
    fullRecordGapCenterValue - 113494,
    fullRecordGapCenterValue - 113362,
    fullRecordGapCenterValue - 113038,
    fullRecordGapCenterValue - 112954,
    fullRecordGapCenterValue - 112738,
    fullRecordGapCenterValue - 112500,
    fullRecordGapCenterValue - 112474,
    fullRecordGapCenterValue - 112198,
    fullRecordGapCenterValue - 112018,
    fullRecordGapCenterValue - 112000,
    fullRecordGapCenterValue - 111934,
    fullRecordGapCenterValue - 111804,
    fullRecordGapCenterValue - 111802,
    fullRecordGapCenterValue - 111634,
    fullRecordGapCenterValue - 111394,
    fullRecordGapCenterValue - 111382,
    fullRecordGapCenterValue - 111334,
    fullRecordGapCenterValue - 111132,
    fullRecordGapCenterValue - 111022,
    fullRecordGapCenterValue - 110914,
    fullRecordGapCenterValue - 110674,
    fullRecordGapCenterValue - 110592,
    fullRecordGapCenterValue - 110458,
    fullRecordGapCenterValue - 110434,
    fullRecordGapCenterValue - 110250,
    fullRecordGapCenterValue - 108898,
    fullRecordGapCenterValue - 108874,
    fullRecordGapCenterValue - 108694,
    fullRecordGapCenterValue - 108502,
    fullRecordGapCenterValue - 107974,
    fullRecordGapCenterValue - 107902,
    fullRecordGapCenterValue - 107854,
    fullRecordGapCenterValue - 107800,
    fullRecordGapCenterValue - 107698,
    fullRecordGapCenterValue - 107662,
    fullRecordGapCenterValue - 107314,
    fullRecordGapCenterValue - 107278,
    fullRecordGapCenterValue - 107218,
    fullRecordGapCenterValue - 107194,
    fullRecordGapCenterValue - 107014,
    fullRecordGapCenterValue - 106722,
    fullRecordGapCenterValue - 106654,
    fullRecordGapCenterValue - 106402,
    fullRecordGapCenterValue - 106342]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00054_fermat : ∀ n ∈ fullRecordGapRow00054_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03393_not_prime : ¬(recordGapCenter - 117358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 117358]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03394_not_prime : ¬(recordGapCenter - 116962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 116962]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03395_not_prime : ¬(recordGapCenter - 116902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 116902]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03396_not_prime : ¬(recordGapCenter - 116878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 116878]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03397_not_prime : ¬(recordGapCenter - 116458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 116458]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03398_not_prime : ¬(recordGapCenter - 116424).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 116424]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03399_not_prime : ¬(recordGapCenter - 116422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 116422]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03400_not_prime : ¬(recordGapCenter - 116134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 116134]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03401_not_prime : ¬(recordGapCenter - 115762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 115762]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03402_not_prime : ¬(recordGapCenter - 115500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 115500]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03403_not_prime : ¬(recordGapCenter - 115114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 115114]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03404_not_prime : ¬(recordGapCenter - 115054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 115054]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03405_not_prime : ¬(recordGapCenter - 114694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 114694]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03406_not_prime : ¬(recordGapCenter - 114658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 114658]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03407_not_prime : ¬(recordGapCenter - 114502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 114502]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03408_not_prime : ¬(recordGapCenter - 114442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 114442]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03409_not_prime : ¬(recordGapCenter - 114298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 114298]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03410_not_prime : ¬(recordGapCenter - 113914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 113914]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03411_not_prime : ¬(recordGapCenter - 113902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 113902]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03412_not_prime : ¬(recordGapCenter - 113794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 113794]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03413_not_prime : ¬(recordGapCenter - 113494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 113494]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03414_not_prime : ¬(recordGapCenter - 113362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 113362]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03415_not_prime : ¬(recordGapCenter - 113038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 113038]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03416_not_prime : ¬(recordGapCenter - 112954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 112954]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03417_not_prime : ¬(recordGapCenter - 112738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 112738]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03418_not_prime : ¬(recordGapCenter - 112500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 112500]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03419_not_prime : ¬(recordGapCenter - 112474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 112474]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03420_not_prime : ¬(recordGapCenter - 112198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 112198]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03421_not_prime : ¬(recordGapCenter - 112018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 112018]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03422_not_prime : ¬(recordGapCenter - 112000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 112000]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03423_not_prime : ¬(recordGapCenter - 111934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111934]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03424_not_prime : ¬(recordGapCenter - 111804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111804]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03425_not_prime : ¬(recordGapCenter - 111802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111802]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03426_not_prime : ¬(recordGapCenter - 111634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111634]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03427_not_prime : ¬(recordGapCenter - 111394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111394]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03428_not_prime : ¬(recordGapCenter - 111382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111382]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03429_not_prime : ¬(recordGapCenter - 111334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111334]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03430_not_prime : ¬(recordGapCenter - 111132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111132]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03431_not_prime : ¬(recordGapCenter - 111022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111022]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03432_not_prime : ¬(recordGapCenter - 110914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 110914]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03433_not_prime : ¬(recordGapCenter - 110674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 110674]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03434_not_prime : ¬(recordGapCenter - 110592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 110592]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03435_not_prime : ¬(recordGapCenter - 110458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 110458]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03436_not_prime : ¬(recordGapCenter - 110434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 110434]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03437_not_prime : ¬(recordGapCenter - 110250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 110250]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03438_not_prime : ¬(recordGapCenter - 108898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 108898]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03439_not_prime : ¬(recordGapCenter - 108874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 108874]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03440_not_prime : ¬(recordGapCenter - 108694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 108694]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03441_not_prime : ¬(recordGapCenter - 108502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 108502]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03442_not_prime : ¬(recordGapCenter - 107974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107974]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03443_not_prime : ¬(recordGapCenter - 107902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107902]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03444_not_prime : ¬(recordGapCenter - 107854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107854]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03445_not_prime : ¬(recordGapCenter - 107800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107800]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03446_not_prime : ¬(recordGapCenter - 107698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107698]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03447_not_prime : ¬(recordGapCenter - 107662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107662]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03448_not_prime : ¬(recordGapCenter - 107314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107314]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03449_not_prime : ¬(recordGapCenter - 107278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107278]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03450_not_prime : ¬(recordGapCenter - 107218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107218]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03451_not_prime : ¬(recordGapCenter - 107194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107194]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03452_not_prime : ¬(recordGapCenter - 107014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107014]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03453_not_prime : ¬(recordGapCenter - 106722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106722]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03454_not_prime : ¬(recordGapCenter - 106654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106654]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03455_not_prime : ¬(recordGapCenter - 106402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106402]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

theorem fullRecordGapTerm03456_not_prime : ¬(recordGapCenter - 106342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106342]
  · apply fullRecordGapRow00054_fermat
    simp [fullRecordGapRow00054_values]

end PrimeFactorUnimodality
