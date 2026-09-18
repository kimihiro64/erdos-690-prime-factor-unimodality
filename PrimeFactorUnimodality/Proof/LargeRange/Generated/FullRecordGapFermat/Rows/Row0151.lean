import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00151_values : List Nat :=
  [fullRecordGapCenterValue + 575726,
    fullRecordGapCenterValue + 575768,
    fullRecordGapCenterValue + 575870,
    fullRecordGapCenterValue + 575922,
    fullRecordGapCenterValue + 575930,
    fullRecordGapCenterValue + 576102,
    fullRecordGapCenterValue + 576276,
    fullRecordGapCenterValue + 576318,
    fullRecordGapCenterValue + 576348,
    fullRecordGapCenterValue + 576362,
    fullRecordGapCenterValue + 576398,
    fullRecordGapCenterValue + 576482,
    fullRecordGapCenterValue + 576698,
    fullRecordGapCenterValue + 576866,
    fullRecordGapCenterValue + 576872,
    fullRecordGapCenterValue + 576942,
    fullRecordGapCenterValue + 576962,
    fullRecordGapCenterValue + 577196,
    fullRecordGapCenterValue + 577292,
    fullRecordGapCenterValue + 577358,
    fullRecordGapCenterValue + 577370,
    fullRecordGapCenterValue + 577398,
    fullRecordGapCenterValue + 577466,
    fullRecordGapCenterValue + 577572,
    fullRecordGapCenterValue + 577578,
    fullRecordGapCenterValue + 577706,
    fullRecordGapCenterValue + 577916,
    fullRecordGapCenterValue + 577938,
    fullRecordGapCenterValue + 577946,
    fullRecordGapCenterValue + 577988,
    fullRecordGapCenterValue + 578030,
    fullRecordGapCenterValue + 578126,
    fullRecordGapCenterValue + 578148,
    fullRecordGapCenterValue + 578316,
    fullRecordGapCenterValue + 578342,
    fullRecordGapCenterValue + 578372,
    fullRecordGapCenterValue + 578390,
    fullRecordGapCenterValue + 578498,
    fullRecordGapCenterValue + 578546,
    fullRecordGapCenterValue + 578742,
    fullRecordGapCenterValue + 578762,
    fullRecordGapCenterValue + 578810,
    fullRecordGapCenterValue + 578846,
    fullRecordGapCenterValue + 578868,
    fullRecordGapCenterValue + 579108,
    fullRecordGapCenterValue + 579162,
    fullRecordGapCenterValue + 579170,
    fullRecordGapCenterValue + 579206,
    fullRecordGapCenterValue + 579356,
    fullRecordGapCenterValue + 579482,
    fullRecordGapCenterValue + 579518,
    fullRecordGapCenterValue + 579596,
    fullRecordGapCenterValue + 579686,
    fullRecordGapCenterValue + 579756,
    fullRecordGapCenterValue + 579848,
    fullRecordGapCenterValue + 579902,
    fullRecordGapCenterValue + 579966,
    fullRecordGapCenterValue + 580002,
    fullRecordGapCenterValue + 580022,
    fullRecordGapCenterValue + 580046,
    fullRecordGapCenterValue + 580226,
    fullRecordGapCenterValue + 580238,
    fullRecordGapCenterValue + 580310,
    fullRecordGapCenterValue + 580386]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00151_fermat : ∀ n ∈ fullRecordGapRow00151_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09601_not_prime : ¬(recordGapCenter + 575726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575726]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09602_not_prime : ¬(recordGapCenter + 575768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575768]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09603_not_prime : ¬(recordGapCenter + 575870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575870]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09604_not_prime : ¬(recordGapCenter + 575922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575922]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09605_not_prime : ¬(recordGapCenter + 575930).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 575930]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09606_not_prime : ¬(recordGapCenter + 576102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576102]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09607_not_prime : ¬(recordGapCenter + 576276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576276]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09608_not_prime : ¬(recordGapCenter + 576318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576318]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09609_not_prime : ¬(recordGapCenter + 576348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576348]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09610_not_prime : ¬(recordGapCenter + 576362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576362]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09611_not_prime : ¬(recordGapCenter + 576398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576398]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09612_not_prime : ¬(recordGapCenter + 576482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576482]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09613_not_prime : ¬(recordGapCenter + 576698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576698]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09614_not_prime : ¬(recordGapCenter + 576866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576866]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09615_not_prime : ¬(recordGapCenter + 576872).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576872]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09616_not_prime : ¬(recordGapCenter + 576942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576942]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09617_not_prime : ¬(recordGapCenter + 576962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 576962]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09618_not_prime : ¬(recordGapCenter + 577196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577196]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09619_not_prime : ¬(recordGapCenter + 577292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577292]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09620_not_prime : ¬(recordGapCenter + 577358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577358]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09621_not_prime : ¬(recordGapCenter + 577370).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577370]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09622_not_prime : ¬(recordGapCenter + 577398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577398]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09623_not_prime : ¬(recordGapCenter + 577466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577466]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09624_not_prime : ¬(recordGapCenter + 577572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577572]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09625_not_prime : ¬(recordGapCenter + 577578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577578]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09626_not_prime : ¬(recordGapCenter + 577706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577706]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09627_not_prime : ¬(recordGapCenter + 577916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577916]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09628_not_prime : ¬(recordGapCenter + 577938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577938]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09629_not_prime : ¬(recordGapCenter + 577946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577946]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09630_not_prime : ¬(recordGapCenter + 577988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 577988]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09631_not_prime : ¬(recordGapCenter + 578030).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578030]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09632_not_prime : ¬(recordGapCenter + 578126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578126]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09633_not_prime : ¬(recordGapCenter + 578148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578148]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09634_not_prime : ¬(recordGapCenter + 578316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578316]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09635_not_prime : ¬(recordGapCenter + 578342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578342]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09636_not_prime : ¬(recordGapCenter + 578372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578372]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09637_not_prime : ¬(recordGapCenter + 578390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578390]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09638_not_prime : ¬(recordGapCenter + 578498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578498]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09639_not_prime : ¬(recordGapCenter + 578546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578546]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09640_not_prime : ¬(recordGapCenter + 578742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578742]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09641_not_prime : ¬(recordGapCenter + 578762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578762]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09642_not_prime : ¬(recordGapCenter + 578810).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578810]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09643_not_prime : ¬(recordGapCenter + 578846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578846]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09644_not_prime : ¬(recordGapCenter + 578868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 578868]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09645_not_prime : ¬(recordGapCenter + 579108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579108]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09646_not_prime : ¬(recordGapCenter + 579162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579162]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09647_not_prime : ¬(recordGapCenter + 579170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579170]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09648_not_prime : ¬(recordGapCenter + 579206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579206]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09649_not_prime : ¬(recordGapCenter + 579356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579356]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09650_not_prime : ¬(recordGapCenter + 579482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579482]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09651_not_prime : ¬(recordGapCenter + 579518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579518]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09652_not_prime : ¬(recordGapCenter + 579596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579596]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09653_not_prime : ¬(recordGapCenter + 579686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579686]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09654_not_prime : ¬(recordGapCenter + 579756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579756]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09655_not_prime : ¬(recordGapCenter + 579848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579848]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09656_not_prime : ¬(recordGapCenter + 579902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579902]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09657_not_prime : ¬(recordGapCenter + 579966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 579966]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09658_not_prime : ¬(recordGapCenter + 580002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580002]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09659_not_prime : ¬(recordGapCenter + 580022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580022]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09660_not_prime : ¬(recordGapCenter + 580046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580046]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09661_not_prime : ¬(recordGapCenter + 580226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580226]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09662_not_prime : ¬(recordGapCenter + 580238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580238]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09663_not_prime : ¬(recordGapCenter + 580310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580310]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

theorem fullRecordGapTerm09664_not_prime : ¬(recordGapCenter + 580386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 580386]
  · apply fullRecordGapRow00151_fermat
    simp [fullRecordGapRow00151_values]

end PrimeFactorUnimodality
