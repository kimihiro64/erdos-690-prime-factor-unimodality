import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00052_values : List Nat :=
  [fullRecordGapCenterValue - 139654,
    fullRecordGapCenterValue - 139642,
    fullRecordGapCenterValue - 139558,
    fullRecordGapCenterValue - 139474,
    fullRecordGapCenterValue - 139078,
    fullRecordGapCenterValue - 138862,
    fullRecordGapCenterValue - 138742,
    fullRecordGapCenterValue - 138682,
    fullRecordGapCenterValue - 138600,
    fullRecordGapCenterValue - 138442,
    fullRecordGapCenterValue - 138394,
    fullRecordGapCenterValue - 138238,
    fullRecordGapCenterValue - 138022,
    fullRecordGapCenterValue - 137794,
    fullRecordGapCenterValue - 137500,
    fullRecordGapCenterValue - 137458,
    fullRecordGapCenterValue - 137374,
    fullRecordGapCenterValue - 137200,
    fullRecordGapCenterValue - 137134,
    fullRecordGapCenterValue - 137062,
    fullRecordGapCenterValue - 136978,
    fullRecordGapCenterValue - 136894,
    fullRecordGapCenterValue - 136702,
    fullRecordGapCenterValue - 136342,
    fullRecordGapCenterValue - 136198,
    fullRecordGapCenterValue - 135658,
    fullRecordGapCenterValue - 135202,
    fullRecordGapCenterValue - 135118,
    fullRecordGapCenterValue - 134998,
    fullRecordGapCenterValue - 134962,
    fullRecordGapCenterValue - 134818,
    fullRecordGapCenterValue - 134782,
    fullRecordGapCenterValue - 134362,
    fullRecordGapCenterValue - 134122,
    fullRecordGapCenterValue - 133954,
    fullRecordGapCenterValue - 133894,
    fullRecordGapCenterValue - 133702,
    fullRecordGapCenterValue - 133650,
    fullRecordGapCenterValue - 133618,
    fullRecordGapCenterValue - 132982,
    fullRecordGapCenterValue - 132898,
    fullRecordGapCenterValue - 132718,
    fullRecordGapCenterValue - 132094,
    fullRecordGapCenterValue - 131962,
    fullRecordGapCenterValue - 131914,
    fullRecordGapCenterValue - 131842,
    fullRecordGapCenterValue - 131712,
    fullRecordGapCenterValue - 131662,
    fullRecordGapCenterValue - 131302,
    fullRecordGapCenterValue - 131250,
    fullRecordGapCenterValue - 131158,
    fullRecordGapCenterValue - 131038,
    fullRecordGapCenterValue - 130680,
    fullRecordGapCenterValue - 130654,
    fullRecordGapCenterValue - 130294,
    fullRecordGapCenterValue - 130258,
    fullRecordGapCenterValue - 129838,
    fullRecordGapCenterValue - 129418,
    fullRecordGapCenterValue - 129360,
    fullRecordGapCenterValue - 129322,
    fullRecordGapCenterValue - 129202,
    fullRecordGapCenterValue - 128434,
    fullRecordGapCenterValue - 128314,
    fullRecordGapCenterValue - 128302]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00052_fermat : ∀ n ∈ fullRecordGapRow00052_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03265_not_prime : ¬(recordGapCenter - 139654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 139654]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03266_not_prime : ¬(recordGapCenter - 139642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 139642]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03267_not_prime : ¬(recordGapCenter - 139558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 139558]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03268_not_prime : ¬(recordGapCenter - 139474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 139474]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03269_not_prime : ¬(recordGapCenter - 139078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 139078]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03270_not_prime : ¬(recordGapCenter - 138862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138862]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03271_not_prime : ¬(recordGapCenter - 138742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138742]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03272_not_prime : ¬(recordGapCenter - 138682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138682]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03273_not_prime : ¬(recordGapCenter - 138600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138600]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03274_not_prime : ¬(recordGapCenter - 138442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138442]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03275_not_prime : ¬(recordGapCenter - 138394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138394]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03276_not_prime : ¬(recordGapCenter - 138238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138238]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03277_not_prime : ¬(recordGapCenter - 138022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 138022]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03278_not_prime : ¬(recordGapCenter - 137794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 137794]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03279_not_prime : ¬(recordGapCenter - 137500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 137500]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03280_not_prime : ¬(recordGapCenter - 137458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 137458]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03281_not_prime : ¬(recordGapCenter - 137374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 137374]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03282_not_prime : ¬(recordGapCenter - 137200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 137200]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03283_not_prime : ¬(recordGapCenter - 137134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 137134]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03284_not_prime : ¬(recordGapCenter - 137062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 137062]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03285_not_prime : ¬(recordGapCenter - 136978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 136978]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03286_not_prime : ¬(recordGapCenter - 136894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 136894]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03287_not_prime : ¬(recordGapCenter - 136702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 136702]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03288_not_prime : ¬(recordGapCenter - 136342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 136342]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03289_not_prime : ¬(recordGapCenter - 136198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 136198]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03290_not_prime : ¬(recordGapCenter - 135658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 135658]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03291_not_prime : ¬(recordGapCenter - 135202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 135202]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03292_not_prime : ¬(recordGapCenter - 135118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 135118]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03293_not_prime : ¬(recordGapCenter - 134998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 134998]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03294_not_prime : ¬(recordGapCenter - 134962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 134962]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03295_not_prime : ¬(recordGapCenter - 134818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 134818]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03296_not_prime : ¬(recordGapCenter - 134782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 134782]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03297_not_prime : ¬(recordGapCenter - 134362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 134362]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03298_not_prime : ¬(recordGapCenter - 134122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 134122]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03299_not_prime : ¬(recordGapCenter - 133954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 133954]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03300_not_prime : ¬(recordGapCenter - 133894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 133894]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03301_not_prime : ¬(recordGapCenter - 133702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 133702]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03302_not_prime : ¬(recordGapCenter - 133650).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 133650]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03303_not_prime : ¬(recordGapCenter - 133618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 133618]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03304_not_prime : ¬(recordGapCenter - 132982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 132982]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03305_not_prime : ¬(recordGapCenter - 132898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 132898]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03306_not_prime : ¬(recordGapCenter - 132718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 132718]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03307_not_prime : ¬(recordGapCenter - 132094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 132094]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03308_not_prime : ¬(recordGapCenter - 131962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131962]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03309_not_prime : ¬(recordGapCenter - 131914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131914]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03310_not_prime : ¬(recordGapCenter - 131842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131842]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03311_not_prime : ¬(recordGapCenter - 131712).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131712]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03312_not_prime : ¬(recordGapCenter - 131662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131662]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03313_not_prime : ¬(recordGapCenter - 131302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131302]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03314_not_prime : ¬(recordGapCenter - 131250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131250]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03315_not_prime : ¬(recordGapCenter - 131158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131158]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03316_not_prime : ¬(recordGapCenter - 131038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 131038]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03317_not_prime : ¬(recordGapCenter - 130680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 130680]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03318_not_prime : ¬(recordGapCenter - 130654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 130654]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03319_not_prime : ¬(recordGapCenter - 130294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 130294]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03320_not_prime : ¬(recordGapCenter - 130258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 130258]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03321_not_prime : ¬(recordGapCenter - 129838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 129838]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03322_not_prime : ¬(recordGapCenter - 129418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 129418]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03323_not_prime : ¬(recordGapCenter - 129360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 129360]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03324_not_prime : ¬(recordGapCenter - 129322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 129322]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03325_not_prime : ¬(recordGapCenter - 129202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 129202]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03326_not_prime : ¬(recordGapCenter - 128434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 128434]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03327_not_prime : ¬(recordGapCenter - 128314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 128314]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

theorem fullRecordGapTerm03328_not_prime : ¬(recordGapCenter - 128302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 128302]
  · apply fullRecordGapRow00052_fermat
    simp [fullRecordGapRow00052_values]

end PrimeFactorUnimodality
