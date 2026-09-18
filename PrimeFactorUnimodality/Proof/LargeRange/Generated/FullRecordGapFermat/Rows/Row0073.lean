import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00073_values : List Nat :=
  [fullRecordGapCenterValue + 179468,
    fullRecordGapCenterValue + 179618,
    fullRecordGapCenterValue + 179708,
    fullRecordGapCenterValue + 179756,
    fullRecordGapCenterValue + 179798,
    fullRecordGapCenterValue + 179852,
    fullRecordGapCenterValue + 179918,
    fullRecordGapCenterValue + 180002,
    fullRecordGapCenterValue + 180146,
    fullRecordGapCenterValue + 180542,
    fullRecordGapCenterValue + 180548,
    fullRecordGapCenterValue + 180716,
    fullRecordGapCenterValue + 180962,
    fullRecordGapCenterValue + 181046,
    fullRecordGapCenterValue + 181052,
    fullRecordGapCenterValue + 181238,
    fullRecordGapCenterValue + 181406,
    fullRecordGapCenterValue + 181646,
    fullRecordGapCenterValue + 181682,
    fullRecordGapCenterValue + 181988,
    fullRecordGapCenterValue + 182018,
    fullRecordGapCenterValue + 182162,
    fullRecordGapCenterValue + 182198,
    fullRecordGapCenterValue + 182228,
    fullRecordGapCenterValue + 182306,
    fullRecordGapCenterValue + 182396,
    fullRecordGapCenterValue + 182498,
    fullRecordGapCenterValue + 182582,
    fullRecordGapCenterValue + 182738,
    fullRecordGapCenterValue + 182828,
    fullRecordGapCenterValue + 182906,
    fullRecordGapCenterValue + 182918,
    fullRecordGapCenterValue + 182952,
    fullRecordGapCenterValue + 183026,
    fullRecordGapCenterValue + 183068,
    fullRecordGapCenterValue + 183332,
    fullRecordGapCenterValue + 183422,
    fullRecordGapCenterValue + 183626,
    fullRecordGapCenterValue + 183750,
    fullRecordGapCenterValue + 183818,
    fullRecordGapCenterValue + 183956,
    fullRecordGapCenterValue + 184166,
    fullRecordGapCenterValue + 184196,
    fullRecordGapCenterValue + 184238,
    fullRecordGapCenterValue + 184286,
    fullRecordGapCenterValue + 184320,
    fullRecordGapCenterValue + 184406,
    fullRecordGapCenterValue + 184502,
    fullRecordGapCenterValue + 184538,
    fullRecordGapCenterValue + 184622,
    fullRecordGapCenterValue + 184800,
    fullRecordGapCenterValue + 184916,
    fullRecordGapCenterValue + 185006,
    fullRecordGapCenterValue + 185102,
    fullRecordGapCenterValue + 185220,
    fullRecordGapCenterValue + 185348,
    fullRecordGapCenterValue + 185582,
    fullRecordGapCenterValue + 185756,
    fullRecordGapCenterValue + 185798,
    fullRecordGapCenterValue + 186092,
    fullRecordGapCenterValue + 186266,
    fullRecordGapCenterValue + 186278,
    fullRecordGapCenterValue + 186302,
    fullRecordGapCenterValue + 186398]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00073_fermat : ∀ n ∈ fullRecordGapRow00073_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04609_not_prime : ¬(recordGapCenter + 179468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179468]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04610_not_prime : ¬(recordGapCenter + 179618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179618]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04611_not_prime : ¬(recordGapCenter + 179708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179708]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04612_not_prime : ¬(recordGapCenter + 179756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179756]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04613_not_prime : ¬(recordGapCenter + 179798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179798]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04614_not_prime : ¬(recordGapCenter + 179852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179852]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04615_not_prime : ¬(recordGapCenter + 179918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 179918]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04616_not_prime : ¬(recordGapCenter + 180002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 180002]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04617_not_prime : ¬(recordGapCenter + 180146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 180146]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04618_not_prime : ¬(recordGapCenter + 180542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 180542]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04619_not_prime : ¬(recordGapCenter + 180548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 180548]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04620_not_prime : ¬(recordGapCenter + 180716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 180716]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04621_not_prime : ¬(recordGapCenter + 180962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 180962]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04622_not_prime : ¬(recordGapCenter + 181046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 181046]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04623_not_prime : ¬(recordGapCenter + 181052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 181052]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04624_not_prime : ¬(recordGapCenter + 181238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 181238]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04625_not_prime : ¬(recordGapCenter + 181406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 181406]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04626_not_prime : ¬(recordGapCenter + 181646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 181646]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04627_not_prime : ¬(recordGapCenter + 181682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 181682]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04628_not_prime : ¬(recordGapCenter + 181988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 181988]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04629_not_prime : ¬(recordGapCenter + 182018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 182018]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04630_not_prime : ¬(recordGapCenter + 182162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 182162]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04631_not_prime : ¬(recordGapCenter + 182198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 182198]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04632_not_prime : ¬(recordGapCenter + 182228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 182228]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04633_not_prime : ¬(recordGapCenter + 182306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 182306]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04634_not_prime : ¬(recordGapCenter + 182396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 182396]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04635_not_prime : ¬(recordGapCenter + 182498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 182498]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04636_not_prime : ¬(recordGapCenter + 182582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 182582]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04637_not_prime : ¬(recordGapCenter + 182738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 182738]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04638_not_prime : ¬(recordGapCenter + 182828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 182828]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04639_not_prime : ¬(recordGapCenter + 182906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 182906]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04640_not_prime : ¬(recordGapCenter + 182918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 182918]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04641_not_prime : ¬(recordGapCenter + 182952).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 182952]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04642_not_prime : ¬(recordGapCenter + 183026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 183026]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04643_not_prime : ¬(recordGapCenter + 183068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 183068]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04644_not_prime : ¬(recordGapCenter + 183332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 183332]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04645_not_prime : ¬(recordGapCenter + 183422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 183422]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04646_not_prime : ¬(recordGapCenter + 183626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 183626]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04647_not_prime : ¬(recordGapCenter + 183750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 183750]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04648_not_prime : ¬(recordGapCenter + 183818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 183818]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04649_not_prime : ¬(recordGapCenter + 183956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 183956]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04650_not_prime : ¬(recordGapCenter + 184166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 184166]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04651_not_prime : ¬(recordGapCenter + 184196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 184196]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04652_not_prime : ¬(recordGapCenter + 184238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 184238]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04653_not_prime : ¬(recordGapCenter + 184286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 184286]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04654_not_prime : ¬(recordGapCenter + 184320).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 184320]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04655_not_prime : ¬(recordGapCenter + 184406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 184406]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04656_not_prime : ¬(recordGapCenter + 184502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 184502]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04657_not_prime : ¬(recordGapCenter + 184538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 184538]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04658_not_prime : ¬(recordGapCenter + 184622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 184622]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04659_not_prime : ¬(recordGapCenter + 184800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 184800]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04660_not_prime : ¬(recordGapCenter + 184916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 184916]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04661_not_prime : ¬(recordGapCenter + 185006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 185006]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04662_not_prime : ¬(recordGapCenter + 185102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 185102]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04663_not_prime : ¬(recordGapCenter + 185220).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 185220]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04664_not_prime : ¬(recordGapCenter + 185348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 185348]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04665_not_prime : ¬(recordGapCenter + 185582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 185582]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04666_not_prime : ¬(recordGapCenter + 185756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 185756]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04667_not_prime : ¬(recordGapCenter + 185798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 185798]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04668_not_prime : ¬(recordGapCenter + 186092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 186092]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04669_not_prime : ¬(recordGapCenter + 186266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 186266]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04670_not_prime : ¬(recordGapCenter + 186278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 186278]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04671_not_prime : ¬(recordGapCenter + 186302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 186302]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

theorem fullRecordGapTerm04672_not_prime : ¬(recordGapCenter + 186398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 186398]
  · apply fullRecordGapRow00073_fermat
    simp [fullRecordGapRow00073_values]

end PrimeFactorUnimodality
