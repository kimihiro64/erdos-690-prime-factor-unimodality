import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00121_values : List Nat :=
  [fullRecordGapCenterValue + 446142,
    fullRecordGapCenterValue + 446210,
    fullRecordGapCenterValue + 446330,
    fullRecordGapCenterValue + 446372,
    fullRecordGapCenterValue + 446510,
    fullRecordGapCenterValue + 446582,
    fullRecordGapCenterValue + 446612,
    fullRecordGapCenterValue + 446646,
    fullRecordGapCenterValue + 446696,
    fullRecordGapCenterValue + 446792,
    fullRecordGapCenterValue + 446870,
    fullRecordGapCenterValue + 446990,
    fullRecordGapCenterValue + 447162,
    fullRecordGapCenterValue + 447186,
    fullRecordGapCenterValue + 447266,
    fullRecordGapCenterValue + 447368,
    fullRecordGapCenterValue + 447438,
    fullRecordGapCenterValue + 447686,
    fullRecordGapCenterValue + 447710,
    fullRecordGapCenterValue + 447738,
    fullRecordGapCenterValue + 447812,
    fullRecordGapCenterValue + 447842,
    fullRecordGapCenterValue + 447878,
    fullRecordGapCenterValue + 447918,
    fullRecordGapCenterValue + 447926,
    fullRecordGapCenterValue + 447998,
    fullRecordGapCenterValue + 448082,
    fullRecordGapCenterValue + 448122,
    fullRecordGapCenterValue + 448142,
    fullRecordGapCenterValue + 448388,
    fullRecordGapCenterValue + 448418,
    fullRecordGapCenterValue + 448556,
    fullRecordGapCenterValue + 448718,
    fullRecordGapCenterValue + 448782,
    fullRecordGapCenterValue + 448802,
    fullRecordGapCenterValue + 448886,
    fullRecordGapCenterValue + 448892,
    fullRecordGapCenterValue + 448922,
    fullRecordGapCenterValue + 448926,
    fullRecordGapCenterValue + 448946,
    fullRecordGapCenterValue + 448988,
    fullRecordGapCenterValue + 449012,
    fullRecordGapCenterValue + 449048,
    fullRecordGapCenterValue + 449058,
    fullRecordGapCenterValue + 449138,
    fullRecordGapCenterValue + 449366,
    fullRecordGapCenterValue + 449396,
    fullRecordGapCenterValue + 449486,
    fullRecordGapCenterValue + 449538,
    fullRecordGapCenterValue + 449598,
    fullRecordGapCenterValue + 449612,
    fullRecordGapCenterValue + 449762,
    fullRecordGapCenterValue + 449870,
    fullRecordGapCenterValue + 449912,
    fullRecordGapCenterValue + 450000,
    fullRecordGapCenterValue + 450066,
    fullRecordGapCenterValue + 450152,
    fullRecordGapCenterValue + 450158,
    fullRecordGapCenterValue + 450266,
    fullRecordGapCenterValue + 450308,
    fullRecordGapCenterValue + 450326,
    fullRecordGapCenterValue + 450560,
    fullRecordGapCenterValue + 450686,
    fullRecordGapCenterValue + 451046]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00121_fermat : ∀ n ∈ fullRecordGapRow00121_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07681_not_prime : ¬(recordGapCenter + 446142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 446142]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07682_not_prime : ¬(recordGapCenter + 446210).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 446210]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07683_not_prime : ¬(recordGapCenter + 446330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 446330]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07684_not_prime : ¬(recordGapCenter + 446372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 446372]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07685_not_prime : ¬(recordGapCenter + 446510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 446510]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07686_not_prime : ¬(recordGapCenter + 446582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 446582]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07687_not_prime : ¬(recordGapCenter + 446612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 446612]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07688_not_prime : ¬(recordGapCenter + 446646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 446646]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07689_not_prime : ¬(recordGapCenter + 446696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 446696]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07690_not_prime : ¬(recordGapCenter + 446792).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 446792]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07691_not_prime : ¬(recordGapCenter + 446870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 446870]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07692_not_prime : ¬(recordGapCenter + 446990).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 446990]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07693_not_prime : ¬(recordGapCenter + 447162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 447162]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07694_not_prime : ¬(recordGapCenter + 447186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 447186]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07695_not_prime : ¬(recordGapCenter + 447266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 447266]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07696_not_prime : ¬(recordGapCenter + 447368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 447368]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07697_not_prime : ¬(recordGapCenter + 447438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 447438]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07698_not_prime : ¬(recordGapCenter + 447686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 447686]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07699_not_prime : ¬(recordGapCenter + 447710).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 447710]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07700_not_prime : ¬(recordGapCenter + 447738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 447738]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07701_not_prime : ¬(recordGapCenter + 447812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 447812]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07702_not_prime : ¬(recordGapCenter + 447842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 447842]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07703_not_prime : ¬(recordGapCenter + 447878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 447878]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07704_not_prime : ¬(recordGapCenter + 447918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 447918]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07705_not_prime : ¬(recordGapCenter + 447926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 447926]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07706_not_prime : ¬(recordGapCenter + 447998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 447998]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07707_not_prime : ¬(recordGapCenter + 448082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448082]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07708_not_prime : ¬(recordGapCenter + 448122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448122]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07709_not_prime : ¬(recordGapCenter + 448142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448142]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07710_not_prime : ¬(recordGapCenter + 448388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448388]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07711_not_prime : ¬(recordGapCenter + 448418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448418]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07712_not_prime : ¬(recordGapCenter + 448556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448556]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07713_not_prime : ¬(recordGapCenter + 448718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448718]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07714_not_prime : ¬(recordGapCenter + 448782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448782]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07715_not_prime : ¬(recordGapCenter + 448802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448802]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07716_not_prime : ¬(recordGapCenter + 448886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448886]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07717_not_prime : ¬(recordGapCenter + 448892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448892]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07718_not_prime : ¬(recordGapCenter + 448922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448922]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07719_not_prime : ¬(recordGapCenter + 448926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448926]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07720_not_prime : ¬(recordGapCenter + 448946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448946]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07721_not_prime : ¬(recordGapCenter + 448988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 448988]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07722_not_prime : ¬(recordGapCenter + 449012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 449012]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07723_not_prime : ¬(recordGapCenter + 449048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 449048]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07724_not_prime : ¬(recordGapCenter + 449058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 449058]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07725_not_prime : ¬(recordGapCenter + 449138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 449138]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07726_not_prime : ¬(recordGapCenter + 449366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 449366]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07727_not_prime : ¬(recordGapCenter + 449396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 449396]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07728_not_prime : ¬(recordGapCenter + 449486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 449486]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07729_not_prime : ¬(recordGapCenter + 449538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 449538]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07730_not_prime : ¬(recordGapCenter + 449598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 449598]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07731_not_prime : ¬(recordGapCenter + 449612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 449612]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07732_not_prime : ¬(recordGapCenter + 449762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 449762]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07733_not_prime : ¬(recordGapCenter + 449870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 449870]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07734_not_prime : ¬(recordGapCenter + 449912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 449912]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07735_not_prime : ¬(recordGapCenter + 450000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 450000]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07736_not_prime : ¬(recordGapCenter + 450066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 450066]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07737_not_prime : ¬(recordGapCenter + 450152).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 450152]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07738_not_prime : ¬(recordGapCenter + 450158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 450158]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07739_not_prime : ¬(recordGapCenter + 450266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 450266]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07740_not_prime : ¬(recordGapCenter + 450308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 450308]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07741_not_prime : ¬(recordGapCenter + 450326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 450326]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07742_not_prime : ¬(recordGapCenter + 450560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 450560]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07743_not_prime : ¬(recordGapCenter + 450686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 450686]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

theorem fullRecordGapTerm07744_not_prime : ¬(recordGapCenter + 451046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 451046]
  · apply fullRecordGapRow00121_fermat
    simp [fullRecordGapRow00121_values]

end PrimeFactorUnimodality
