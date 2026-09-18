import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00049_values : List Nat :=
  [fullRecordGapCenterValue - 173002,
    fullRecordGapCenterValue - 172828,
    fullRecordGapCenterValue - 172804,
    fullRecordGapCenterValue - 172762,
    fullRecordGapCenterValue - 172714,
    fullRecordGapCenterValue - 172498,
    fullRecordGapCenterValue - 172402,
    fullRecordGapCenterValue - 171982,
    fullRecordGapCenterValue - 171694,
    fullRecordGapCenterValue - 171562,
    fullRecordGapCenterValue - 171502,
    fullRecordGapCenterValue - 171334,
    fullRecordGapCenterValue - 171238,
    fullRecordGapCenterValue - 171154,
    fullRecordGapCenterValue - 171034,
    fullRecordGapCenterValue - 170902,
    fullRecordGapCenterValue - 170854,
    fullRecordGapCenterValue - 170518,
    fullRecordGapCenterValue - 170494,
    fullRecordGapCenterValue - 170182,
    fullRecordGapCenterValue - 170100,
    fullRecordGapCenterValue - 169894,
    fullRecordGapCenterValue - 169738,
    fullRecordGapCenterValue - 169654,
    fullRecordGapCenterValue - 169522,
    fullRecordGapCenterValue - 169402,
    fullRecordGapCenterValue - 169258,
    fullRecordGapCenterValue - 169102,
    fullRecordGapCenterValue - 169018,
    fullRecordGapCenterValue - 168934,
    fullRecordGapCenterValue - 168802,
    fullRecordGapCenterValue - 168754,
    fullRecordGapCenterValue - 168598,
    fullRecordGapCenterValue - 168094,
    fullRecordGapCenterValue - 168034,
    fullRecordGapCenterValue - 167554,
    fullRecordGapCenterValue - 167242,
    fullRecordGapCenterValue - 167158,
    fullRecordGapCenterValue - 167122,
    fullRecordGapCenterValue - 166942,
    fullRecordGapCenterValue - 166798,
    fullRecordGapCenterValue - 166714,
    fullRecordGapCenterValue - 166534,
    fullRecordGapCenterValue - 166462,
    fullRecordGapCenterValue - 166012,
    fullRecordGapCenterValue - 165778,
    fullRecordGapCenterValue - 165622,
    fullRecordGapCenterValue - 165562,
    fullRecordGapCenterValue - 165442,
    fullRecordGapCenterValue - 165238,
    fullRecordGapCenterValue - 165058,
    fullRecordGapCenterValue - 164698,
    fullRecordGapCenterValue - 164482,
    fullRecordGapCenterValue - 164434,
    fullRecordGapCenterValue - 164062,
    fullRecordGapCenterValue - 163942,
    fullRecordGapCenterValue - 163840,
    fullRecordGapCenterValue - 163678,
    fullRecordGapCenterValue - 163522,
    fullRecordGapCenterValue - 163414,
    fullRecordGapCenterValue - 163342,
    fullRecordGapCenterValue - 163294,
    fullRecordGapCenterValue - 163258,
    fullRecordGapCenterValue - 163138]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00049_fermat : ∀ n ∈ fullRecordGapRow00049_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03073_not_prime : ¬(recordGapCenter - 173002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 173002]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03074_not_prime : ¬(recordGapCenter - 172828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 172828]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03075_not_prime : ¬(recordGapCenter - 172804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 172804]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03076_not_prime : ¬(recordGapCenter - 172762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 172762]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03077_not_prime : ¬(recordGapCenter - 172714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 172714]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03078_not_prime : ¬(recordGapCenter - 172498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 172498]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03079_not_prime : ¬(recordGapCenter - 172402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 172402]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03080_not_prime : ¬(recordGapCenter - 171982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171982]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03081_not_prime : ¬(recordGapCenter - 171694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171694]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03082_not_prime : ¬(recordGapCenter - 171562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171562]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03083_not_prime : ¬(recordGapCenter - 171502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171502]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03084_not_prime : ¬(recordGapCenter - 171334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171334]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03085_not_prime : ¬(recordGapCenter - 171238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171238]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03086_not_prime : ¬(recordGapCenter - 171154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171154]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03087_not_prime : ¬(recordGapCenter - 171034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 171034]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03088_not_prime : ¬(recordGapCenter - 170902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 170902]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03089_not_prime : ¬(recordGapCenter - 170854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 170854]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03090_not_prime : ¬(recordGapCenter - 170518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 170518]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03091_not_prime : ¬(recordGapCenter - 170494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 170494]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03092_not_prime : ¬(recordGapCenter - 170182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 170182]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03093_not_prime : ¬(recordGapCenter - 170100).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 170100]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03094_not_prime : ¬(recordGapCenter - 169894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169894]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03095_not_prime : ¬(recordGapCenter - 169738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169738]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03096_not_prime : ¬(recordGapCenter - 169654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169654]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03097_not_prime : ¬(recordGapCenter - 169522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169522]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03098_not_prime : ¬(recordGapCenter - 169402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169402]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03099_not_prime : ¬(recordGapCenter - 169258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169258]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03100_not_prime : ¬(recordGapCenter - 169102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169102]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03101_not_prime : ¬(recordGapCenter - 169018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 169018]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03102_not_prime : ¬(recordGapCenter - 168934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 168934]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03103_not_prime : ¬(recordGapCenter - 168802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 168802]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03104_not_prime : ¬(recordGapCenter - 168754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 168754]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03105_not_prime : ¬(recordGapCenter - 168598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 168598]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03106_not_prime : ¬(recordGapCenter - 168094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 168094]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03107_not_prime : ¬(recordGapCenter - 168034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 168034]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03108_not_prime : ¬(recordGapCenter - 167554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 167554]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03109_not_prime : ¬(recordGapCenter - 167242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 167242]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03110_not_prime : ¬(recordGapCenter - 167158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 167158]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03111_not_prime : ¬(recordGapCenter - 167122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 167122]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03112_not_prime : ¬(recordGapCenter - 166942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 166942]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03113_not_prime : ¬(recordGapCenter - 166798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 166798]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03114_not_prime : ¬(recordGapCenter - 166714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 166714]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03115_not_prime : ¬(recordGapCenter - 166534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 166534]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03116_not_prime : ¬(recordGapCenter - 166462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 166462]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03117_not_prime : ¬(recordGapCenter - 166012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 166012]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03118_not_prime : ¬(recordGapCenter - 165778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 165778]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03119_not_prime : ¬(recordGapCenter - 165622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 165622]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03120_not_prime : ¬(recordGapCenter - 165562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 165562]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03121_not_prime : ¬(recordGapCenter - 165442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 165442]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03122_not_prime : ¬(recordGapCenter - 165238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 165238]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03123_not_prime : ¬(recordGapCenter - 165058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 165058]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03124_not_prime : ¬(recordGapCenter - 164698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 164698]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03125_not_prime : ¬(recordGapCenter - 164482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 164482]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03126_not_prime : ¬(recordGapCenter - 164434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 164434]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03127_not_prime : ¬(recordGapCenter - 164062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 164062]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03128_not_prime : ¬(recordGapCenter - 163942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163942]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03129_not_prime : ¬(recordGapCenter - 163840).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163840]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03130_not_prime : ¬(recordGapCenter - 163678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163678]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03131_not_prime : ¬(recordGapCenter - 163522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163522]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03132_not_prime : ¬(recordGapCenter - 163414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163414]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03133_not_prime : ¬(recordGapCenter - 163342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163342]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03134_not_prime : ¬(recordGapCenter - 163294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163294]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03135_not_prime : ¬(recordGapCenter - 163258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163258]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

theorem fullRecordGapTerm03136_not_prime : ¬(recordGapCenter - 163138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 163138]
  · apply fullRecordGapRow00049_fermat
    simp [fullRecordGapRow00049_values]

end PrimeFactorUnimodality
