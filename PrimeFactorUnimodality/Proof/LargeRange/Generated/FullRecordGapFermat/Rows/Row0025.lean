import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00025_values : List Nat :=
  [fullRecordGapCenterValue - 333714,
    fullRecordGapCenterValue - 333694,
    fullRecordGapCenterValue - 333682,
    fullRecordGapCenterValue - 333618,
    fullRecordGapCenterValue - 333604,
    fullRecordGapCenterValue - 333478,
    fullRecordGapCenterValue - 333364,
    fullRecordGapCenterValue - 333262,
    fullRecordGapCenterValue - 333202,
    fullRecordGapCenterValue - 333028,
    fullRecordGapCenterValue - 332922,
    fullRecordGapCenterValue - 332884,
    fullRecordGapCenterValue - 332814,
    fullRecordGapCenterValue - 332742,
    fullRecordGapCenterValue - 332394,
    fullRecordGapCenterValue - 332058,
    fullRecordGapCenterValue - 331924,
    fullRecordGapCenterValue - 331774,
    fullRecordGapCenterValue - 331714,
    fullRecordGapCenterValue - 331564,
    fullRecordGapCenterValue - 331494,
    fullRecordGapCenterValue - 331438,
    fullRecordGapCenterValue - 331252,
    fullRecordGapCenterValue - 331242,
    fullRecordGapCenterValue - 331222,
    fullRecordGapCenterValue - 331174,
    fullRecordGapCenterValue - 331138,
    fullRecordGapCenterValue - 331102,
    fullRecordGapCenterValue - 331054,
    fullRecordGapCenterValue - 330978,
    fullRecordGapCenterValue - 330762,
    fullRecordGapCenterValue - 330750,
    fullRecordGapCenterValue - 330628,
    fullRecordGapCenterValue - 330364,
    fullRecordGapCenterValue - 330178,
    fullRecordGapCenterValue - 330082,
    fullRecordGapCenterValue - 330028,
    fullRecordGapCenterValue - 330000,
    fullRecordGapCenterValue - 329898,
    fullRecordGapCenterValue - 329838,
    fullRecordGapCenterValue - 329578,
    fullRecordGapCenterValue - 329572,
    fullRecordGapCenterValue - 329502,
    fullRecordGapCenterValue - 329404,
    fullRecordGapCenterValue - 329280,
    fullRecordGapCenterValue - 329214,
    fullRecordGapCenterValue - 329068,
    fullRecordGapCenterValue - 329044,
    fullRecordGapCenterValue - 328954,
    fullRecordGapCenterValue - 328894,
    fullRecordGapCenterValue - 328858,
    fullRecordGapCenterValue - 328732,
    fullRecordGapCenterValue - 328722,
    fullRecordGapCenterValue - 328612,
    fullRecordGapCenterValue - 328564,
    fullRecordGapCenterValue - 328534,
    fullRecordGapCenterValue - 328362,
    fullRecordGapCenterValue - 328278,
    fullRecordGapCenterValue - 328234,
    fullRecordGapCenterValue - 328204,
    fullRecordGapCenterValue - 328114,
    fullRecordGapCenterValue - 328102,
    fullRecordGapCenterValue - 328038,
    fullRecordGapCenterValue - 327994]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00025_fermat : ∀ n ∈ fullRecordGapRow00025_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01537_not_prime : ¬(recordGapCenter - 333714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333714]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01538_not_prime : ¬(recordGapCenter - 333694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333694]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01539_not_prime : ¬(recordGapCenter - 333682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333682]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01540_not_prime : ¬(recordGapCenter - 333618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333618]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01541_not_prime : ¬(recordGapCenter - 333604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333604]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01542_not_prime : ¬(recordGapCenter - 333478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333478]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01543_not_prime : ¬(recordGapCenter - 333364).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333364]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01544_not_prime : ¬(recordGapCenter - 333262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333262]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01545_not_prime : ¬(recordGapCenter - 333202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333202]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01546_not_prime : ¬(recordGapCenter - 333028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 333028]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01547_not_prime : ¬(recordGapCenter - 332922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 332922]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01548_not_prime : ¬(recordGapCenter - 332884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 332884]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01549_not_prime : ¬(recordGapCenter - 332814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 332814]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01550_not_prime : ¬(recordGapCenter - 332742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 332742]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01551_not_prime : ¬(recordGapCenter - 332394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 332394]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01552_not_prime : ¬(recordGapCenter - 332058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 332058]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01553_not_prime : ¬(recordGapCenter - 331924).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331924]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01554_not_prime : ¬(recordGapCenter - 331774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331774]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01555_not_prime : ¬(recordGapCenter - 331714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331714]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01556_not_prime : ¬(recordGapCenter - 331564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331564]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01557_not_prime : ¬(recordGapCenter - 331494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331494]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01558_not_prime : ¬(recordGapCenter - 331438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331438]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01559_not_prime : ¬(recordGapCenter - 331252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331252]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01560_not_prime : ¬(recordGapCenter - 331242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331242]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01561_not_prime : ¬(recordGapCenter - 331222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331222]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01562_not_prime : ¬(recordGapCenter - 331174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331174]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01563_not_prime : ¬(recordGapCenter - 331138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331138]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01564_not_prime : ¬(recordGapCenter - 331102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331102]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01565_not_prime : ¬(recordGapCenter - 331054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 331054]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01566_not_prime : ¬(recordGapCenter - 330978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330978]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01567_not_prime : ¬(recordGapCenter - 330762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330762]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01568_not_prime : ¬(recordGapCenter - 330750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330750]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01569_not_prime : ¬(recordGapCenter - 330628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330628]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01570_not_prime : ¬(recordGapCenter - 330364).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330364]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01571_not_prime : ¬(recordGapCenter - 330178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330178]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01572_not_prime : ¬(recordGapCenter - 330082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330082]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01573_not_prime : ¬(recordGapCenter - 330028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330028]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01574_not_prime : ¬(recordGapCenter - 330000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 330000]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01575_not_prime : ¬(recordGapCenter - 329898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329898]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01576_not_prime : ¬(recordGapCenter - 329838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329838]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01577_not_prime : ¬(recordGapCenter - 329578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329578]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01578_not_prime : ¬(recordGapCenter - 329572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329572]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01579_not_prime : ¬(recordGapCenter - 329502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329502]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01580_not_prime : ¬(recordGapCenter - 329404).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329404]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01581_not_prime : ¬(recordGapCenter - 329280).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329280]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01582_not_prime : ¬(recordGapCenter - 329214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329214]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01583_not_prime : ¬(recordGapCenter - 329068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329068]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01584_not_prime : ¬(recordGapCenter - 329044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 329044]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01585_not_prime : ¬(recordGapCenter - 328954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328954]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01586_not_prime : ¬(recordGapCenter - 328894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328894]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01587_not_prime : ¬(recordGapCenter - 328858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328858]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01588_not_prime : ¬(recordGapCenter - 328732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328732]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01589_not_prime : ¬(recordGapCenter - 328722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328722]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01590_not_prime : ¬(recordGapCenter - 328612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328612]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01591_not_prime : ¬(recordGapCenter - 328564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328564]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01592_not_prime : ¬(recordGapCenter - 328534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328534]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01593_not_prime : ¬(recordGapCenter - 328362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328362]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01594_not_prime : ¬(recordGapCenter - 328278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328278]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01595_not_prime : ¬(recordGapCenter - 328234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328234]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01596_not_prime : ¬(recordGapCenter - 328204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328204]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01597_not_prime : ¬(recordGapCenter - 328114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328114]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01598_not_prime : ¬(recordGapCenter - 328102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328102]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01599_not_prime : ¬(recordGapCenter - 328038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 328038]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

theorem fullRecordGapTerm01600_not_prime : ¬(recordGapCenter - 327994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 327994]
  · apply fullRecordGapRow00025_fermat
    simp [fullRecordGapRow00025_values]

end PrimeFactorUnimodality
