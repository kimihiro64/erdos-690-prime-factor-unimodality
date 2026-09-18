import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00167_values : List Nat :=
  [fullRecordGapCenterValue + 641442,
    fullRecordGapCenterValue + 641492,
    fullRecordGapCenterValue + 641522,
    fullRecordGapCenterValue + 641588,
    fullRecordGapCenterValue + 641636,
    fullRecordGapCenterValue + 641672,
    fullRecordGapCenterValue + 641678,
    fullRecordGapCenterValue + 642036,
    fullRecordGapCenterValue + 642126,
    fullRecordGapCenterValue + 642146,
    fullRecordGapCenterValue + 642338,
    fullRecordGapCenterValue + 642398,
    fullRecordGapCenterValue + 642548,
    fullRecordGapCenterValue + 642588,
    fullRecordGapCenterValue + 642596,
    fullRecordGapCenterValue + 642612,
    fullRecordGapCenterValue + 642626,
    fullRecordGapCenterValue + 642632,
    fullRecordGapCenterValue + 642710,
    fullRecordGapCenterValue + 642738,
    fullRecordGapCenterValue + 642806,
    fullRecordGapCenterValue + 642822,
    fullRecordGapCenterValue + 642938,
    fullRecordGapCenterValue + 642978,
    fullRecordGapCenterValue + 643028,
    fullRecordGapCenterValue + 643092,
    fullRecordGapCenterValue + 643098,
    fullRecordGapCenterValue + 643106,
    fullRecordGapCenterValue + 643116,
    fullRecordGapCenterValue + 643142,
    fullRecordGapCenterValue + 643182,
    fullRecordGapCenterValue + 643190,
    fullRecordGapCenterValue + 643202,
    fullRecordGapCenterValue + 643262,
    fullRecordGapCenterValue + 643268,
    fullRecordGapCenterValue + 643308,
    fullRecordGapCenterValue + 643316,
    fullRecordGapCenterValue + 643322,
    fullRecordGapCenterValue + 643332,
    fullRecordGapCenterValue + 643458,
    fullRecordGapCenterValue + 643508,
    fullRecordGapCenterValue + 643532,
    fullRecordGapCenterValue + 643592,
    fullRecordGapCenterValue + 643638,
    fullRecordGapCenterValue + 643668,
    fullRecordGapCenterValue + 643730,
    fullRecordGapCenterValue + 643778,
    fullRecordGapCenterValue + 643802,
    fullRecordGapCenterValue + 643868,
    fullRecordGapCenterValue + 643898,
    fullRecordGapCenterValue + 644018,
    fullRecordGapCenterValue + 644030,
    fullRecordGapCenterValue + 644036,
    fullRecordGapCenterValue + 644078,
    fullRecordGapCenterValue + 644186,
    fullRecordGapCenterValue + 644316,
    fullRecordGapCenterValue + 644348,
    fullRecordGapCenterValue + 644388,
    fullRecordGapCenterValue + 644390,
    fullRecordGapCenterValue + 644498,
    fullRecordGapCenterValue + 644702,
    fullRecordGapCenterValue + 644718,
    fullRecordGapCenterValue + 644792,
    fullRecordGapCenterValue + 644918]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00167_fermat : ∀ n ∈ fullRecordGapRow00167_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10625_not_prime : ¬(recordGapCenter + 641442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641442]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10626_not_prime : ¬(recordGapCenter + 641492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641492]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10627_not_prime : ¬(recordGapCenter + 641522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641522]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10628_not_prime : ¬(recordGapCenter + 641588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641588]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10629_not_prime : ¬(recordGapCenter + 641636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641636]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10630_not_prime : ¬(recordGapCenter + 641672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641672]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10631_not_prime : ¬(recordGapCenter + 641678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 641678]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10632_not_prime : ¬(recordGapCenter + 642036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642036]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10633_not_prime : ¬(recordGapCenter + 642126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642126]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10634_not_prime : ¬(recordGapCenter + 642146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642146]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10635_not_prime : ¬(recordGapCenter + 642338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642338]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10636_not_prime : ¬(recordGapCenter + 642398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642398]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10637_not_prime : ¬(recordGapCenter + 642548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642548]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10638_not_prime : ¬(recordGapCenter + 642588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642588]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10639_not_prime : ¬(recordGapCenter + 642596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642596]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10640_not_prime : ¬(recordGapCenter + 642612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642612]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10641_not_prime : ¬(recordGapCenter + 642626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642626]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10642_not_prime : ¬(recordGapCenter + 642632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642632]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10643_not_prime : ¬(recordGapCenter + 642710).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642710]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10644_not_prime : ¬(recordGapCenter + 642738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642738]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10645_not_prime : ¬(recordGapCenter + 642806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642806]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10646_not_prime : ¬(recordGapCenter + 642822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642822]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10647_not_prime : ¬(recordGapCenter + 642938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642938]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10648_not_prime : ¬(recordGapCenter + 642978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 642978]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10649_not_prime : ¬(recordGapCenter + 643028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643028]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10650_not_prime : ¬(recordGapCenter + 643092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643092]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10651_not_prime : ¬(recordGapCenter + 643098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643098]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10652_not_prime : ¬(recordGapCenter + 643106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643106]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10653_not_prime : ¬(recordGapCenter + 643116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643116]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10654_not_prime : ¬(recordGapCenter + 643142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643142]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10655_not_prime : ¬(recordGapCenter + 643182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643182]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10656_not_prime : ¬(recordGapCenter + 643190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643190]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10657_not_prime : ¬(recordGapCenter + 643202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643202]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10658_not_prime : ¬(recordGapCenter + 643262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643262]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10659_not_prime : ¬(recordGapCenter + 643268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643268]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10660_not_prime : ¬(recordGapCenter + 643308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643308]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10661_not_prime : ¬(recordGapCenter + 643316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643316]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10662_not_prime : ¬(recordGapCenter + 643322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643322]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10663_not_prime : ¬(recordGapCenter + 643332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643332]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10664_not_prime : ¬(recordGapCenter + 643458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643458]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10665_not_prime : ¬(recordGapCenter + 643508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643508]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10666_not_prime : ¬(recordGapCenter + 643532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643532]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10667_not_prime : ¬(recordGapCenter + 643592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643592]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10668_not_prime : ¬(recordGapCenter + 643638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643638]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10669_not_prime : ¬(recordGapCenter + 643668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643668]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10670_not_prime : ¬(recordGapCenter + 643730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643730]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10671_not_prime : ¬(recordGapCenter + 643778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643778]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10672_not_prime : ¬(recordGapCenter + 643802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643802]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10673_not_prime : ¬(recordGapCenter + 643868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643868]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10674_not_prime : ¬(recordGapCenter + 643898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 643898]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10675_not_prime : ¬(recordGapCenter + 644018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644018]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10676_not_prime : ¬(recordGapCenter + 644030).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644030]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10677_not_prime : ¬(recordGapCenter + 644036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644036]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10678_not_prime : ¬(recordGapCenter + 644078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644078]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10679_not_prime : ¬(recordGapCenter + 644186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644186]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10680_not_prime : ¬(recordGapCenter + 644316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644316]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10681_not_prime : ¬(recordGapCenter + 644348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644348]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10682_not_prime : ¬(recordGapCenter + 644388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644388]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10683_not_prime : ¬(recordGapCenter + 644390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644390]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10684_not_prime : ¬(recordGapCenter + 644498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644498]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10685_not_prime : ¬(recordGapCenter + 644702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644702]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10686_not_prime : ¬(recordGapCenter + 644718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644718]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10687_not_prime : ¬(recordGapCenter + 644792).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644792]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

theorem fullRecordGapTerm10688_not_prime : ¬(recordGapCenter + 644918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 644918]
  · apply fullRecordGapRow00167_fermat
    simp [fullRecordGapRow00167_values]

end PrimeFactorUnimodality
