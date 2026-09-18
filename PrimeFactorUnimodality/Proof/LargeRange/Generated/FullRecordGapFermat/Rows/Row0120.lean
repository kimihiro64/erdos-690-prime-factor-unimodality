import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00120_values : List Nat :=
  [fullRecordGapCenterValue + 441992,
    fullRecordGapCenterValue + 442158,
    fullRecordGapCenterValue + 442172,
    fullRecordGapCenterValue + 442268,
    fullRecordGapCenterValue + 442418,
    fullRecordGapCenterValue + 442466,
    fullRecordGapCenterValue + 442478,
    fullRecordGapCenterValue + 442626,
    fullRecordGapCenterValue + 442698,
    fullRecordGapCenterValue + 442808,
    fullRecordGapCenterValue + 442916,
    fullRecordGapCenterValue + 443012,
    fullRecordGapCenterValue + 443018,
    fullRecordGapCenterValue + 443048,
    fullRecordGapCenterValue + 443082,
    fullRecordGapCenterValue + 443192,
    fullRecordGapCenterValue + 443306,
    fullRecordGapCenterValue + 443396,
    fullRecordGapCenterValue + 443426,
    fullRecordGapCenterValue + 443438,
    fullRecordGapCenterValue + 443528,
    fullRecordGapCenterValue + 443570,
    fullRecordGapCenterValue + 443636,
    fullRecordGapCenterValue + 443658,
    fullRecordGapCenterValue + 443882,
    fullRecordGapCenterValue + 444008,
    fullRecordGapCenterValue + 444126,
    fullRecordGapCenterValue + 444162,
    fullRecordGapCenterValue + 444326,
    fullRecordGapCenterValue + 444386,
    fullRecordGapCenterValue + 444398,
    fullRecordGapCenterValue + 444426,
    fullRecordGapCenterValue + 444476,
    fullRecordGapCenterValue + 444530,
    fullRecordGapCenterValue + 444558,
    fullRecordGapCenterValue + 444806,
    fullRecordGapCenterValue + 444908,
    fullRecordGapCenterValue + 444966,
    fullRecordGapCenterValue + 444998,
    fullRecordGapCenterValue + 445002,
    fullRecordGapCenterValue + 445022,
    fullRecordGapCenterValue + 445070,
    fullRecordGapCenterValue + 445106,
    fullRecordGapCenterValue + 445112,
    fullRecordGapCenterValue + 445182,
    fullRecordGapCenterValue + 445202,
    fullRecordGapCenterValue + 445226,
    fullRecordGapCenterValue + 445268,
    fullRecordGapCenterValue + 445292,
    fullRecordGapCenterValue + 445358,
    fullRecordGapCenterValue + 445448,
    fullRecordGapCenterValue + 445490,
    fullRecordGapCenterValue + 445646,
    fullRecordGapCenterValue + 445722,
    fullRecordGapCenterValue + 445736,
    fullRecordGapCenterValue + 445772,
    fullRecordGapCenterValue + 445790,
    fullRecordGapCenterValue + 445838,
    fullRecordGapCenterValue + 445862,
    fullRecordGapCenterValue + 445868,
    fullRecordGapCenterValue + 445902,
    fullRecordGapCenterValue + 445938,
    fullRecordGapCenterValue + 445982,
    fullRecordGapCenterValue + 446036]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00120_fermat : ∀ n ∈ fullRecordGapRow00120_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07617_not_prime : ¬(recordGapCenter + 441992).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 441992]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07618_not_prime : ¬(recordGapCenter + 442158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 442158]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07619_not_prime : ¬(recordGapCenter + 442172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 442172]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07620_not_prime : ¬(recordGapCenter + 442268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 442268]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07621_not_prime : ¬(recordGapCenter + 442418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 442418]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07622_not_prime : ¬(recordGapCenter + 442466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 442466]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07623_not_prime : ¬(recordGapCenter + 442478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 442478]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07624_not_prime : ¬(recordGapCenter + 442626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 442626]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07625_not_prime : ¬(recordGapCenter + 442698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 442698]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07626_not_prime : ¬(recordGapCenter + 442808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 442808]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07627_not_prime : ¬(recordGapCenter + 442916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 442916]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07628_not_prime : ¬(recordGapCenter + 443012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 443012]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07629_not_prime : ¬(recordGapCenter + 443018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 443018]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07630_not_prime : ¬(recordGapCenter + 443048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 443048]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07631_not_prime : ¬(recordGapCenter + 443082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 443082]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07632_not_prime : ¬(recordGapCenter + 443192).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 443192]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07633_not_prime : ¬(recordGapCenter + 443306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 443306]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07634_not_prime : ¬(recordGapCenter + 443396).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 443396]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07635_not_prime : ¬(recordGapCenter + 443426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 443426]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07636_not_prime : ¬(recordGapCenter + 443438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 443438]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07637_not_prime : ¬(recordGapCenter + 443528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 443528]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07638_not_prime : ¬(recordGapCenter + 443570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 443570]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07639_not_prime : ¬(recordGapCenter + 443636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 443636]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07640_not_prime : ¬(recordGapCenter + 443658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 443658]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07641_not_prime : ¬(recordGapCenter + 443882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 443882]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07642_not_prime : ¬(recordGapCenter + 444008).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 444008]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07643_not_prime : ¬(recordGapCenter + 444126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 444126]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07644_not_prime : ¬(recordGapCenter + 444162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 444162]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07645_not_prime : ¬(recordGapCenter + 444326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 444326]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07646_not_prime : ¬(recordGapCenter + 444386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 444386]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07647_not_prime : ¬(recordGapCenter + 444398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 444398]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07648_not_prime : ¬(recordGapCenter + 444426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 444426]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07649_not_prime : ¬(recordGapCenter + 444476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 444476]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07650_not_prime : ¬(recordGapCenter + 444530).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 444530]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07651_not_prime : ¬(recordGapCenter + 444558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 444558]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07652_not_prime : ¬(recordGapCenter + 444806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 444806]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07653_not_prime : ¬(recordGapCenter + 444908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 444908]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07654_not_prime : ¬(recordGapCenter + 444966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 444966]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07655_not_prime : ¬(recordGapCenter + 444998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 444998]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07656_not_prime : ¬(recordGapCenter + 445002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445002]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07657_not_prime : ¬(recordGapCenter + 445022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445022]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07658_not_prime : ¬(recordGapCenter + 445070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445070]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07659_not_prime : ¬(recordGapCenter + 445106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445106]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07660_not_prime : ¬(recordGapCenter + 445112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445112]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07661_not_prime : ¬(recordGapCenter + 445182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445182]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07662_not_prime : ¬(recordGapCenter + 445202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445202]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07663_not_prime : ¬(recordGapCenter + 445226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445226]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07664_not_prime : ¬(recordGapCenter + 445268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445268]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07665_not_prime : ¬(recordGapCenter + 445292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445292]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07666_not_prime : ¬(recordGapCenter + 445358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445358]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07667_not_prime : ¬(recordGapCenter + 445448).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445448]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07668_not_prime : ¬(recordGapCenter + 445490).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445490]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07669_not_prime : ¬(recordGapCenter + 445646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445646]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07670_not_prime : ¬(recordGapCenter + 445722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445722]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07671_not_prime : ¬(recordGapCenter + 445736).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445736]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07672_not_prime : ¬(recordGapCenter + 445772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445772]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07673_not_prime : ¬(recordGapCenter + 445790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445790]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07674_not_prime : ¬(recordGapCenter + 445838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445838]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07675_not_prime : ¬(recordGapCenter + 445862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445862]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07676_not_prime : ¬(recordGapCenter + 445868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445868]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07677_not_prime : ¬(recordGapCenter + 445902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445902]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07678_not_prime : ¬(recordGapCenter + 445938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445938]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07679_not_prime : ¬(recordGapCenter + 445982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 445982]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

theorem fullRecordGapTerm07680_not_prime : ¬(recordGapCenter + 446036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 446036]
  · apply fullRecordGapRow00120_fermat
    simp [fullRecordGapRow00120_values]

end PrimeFactorUnimodality
