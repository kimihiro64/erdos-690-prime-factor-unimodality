import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00056_values : List Nat :=
  [fullRecordGapCenterValue - 95962,
    fullRecordGapCenterValue - 95878,
    fullRecordGapCenterValue - 95554,
    fullRecordGapCenterValue - 95482,
    fullRecordGapCenterValue - 95434,
    fullRecordGapCenterValue - 95422,
    fullRecordGapCenterValue - 95398,
    fullRecordGapCenterValue - 95218,
    fullRecordGapCenterValue - 94918,
    fullRecordGapCenterValue - 94864,
    fullRecordGapCenterValue - 94762,
    fullRecordGapCenterValue - 94702,
    fullRecordGapCenterValue - 94678,
    fullRecordGapCenterValue - 94500,
    fullRecordGapCenterValue - 94474,
    fullRecordGapCenterValue - 94258,
    fullRecordGapCenterValue - 93994,
    fullRecordGapCenterValue - 93838,
    fullRecordGapCenterValue - 93778,
    fullRecordGapCenterValue - 93634,
    fullRecordGapCenterValue - 93538,
    fullRecordGapCenterValue - 93358,
    fullRecordGapCenterValue - 93312,
    fullRecordGapCenterValue - 93202,
    fullRecordGapCenterValue - 93022,
    fullRecordGapCenterValue - 92914,
    fullRecordGapCenterValue - 92698,
    fullRecordGapCenterValue - 92614,
    fullRecordGapCenterValue - 92398,
    fullRecordGapCenterValue - 92374,
    fullRecordGapCenterValue - 92182,
    fullRecordGapCenterValue - 92160,
    fullRecordGapCenterValue - 92098,
    fullRecordGapCenterValue - 91774,
    fullRecordGapCenterValue - 91738,
    fullRecordGapCenterValue - 91654,
    fullRecordGapCenterValue - 91534,
    fullRecordGapCenterValue - 91138,
    fullRecordGapCenterValue - 91114,
    fullRecordGapCenterValue - 90778,
    fullRecordGapCenterValue - 90720,
    fullRecordGapCenterValue - 90634,
    fullRecordGapCenterValue - 90562,
    fullRecordGapCenterValue - 90382,
    fullRecordGapCenterValue - 90274,
    fullRecordGapCenterValue - 90262,
    fullRecordGapCenterValue - 89878,
    fullRecordGapCenterValue - 89758,
    fullRecordGapCenterValue - 89638,
    fullRecordGapCenterValue - 89578,
    fullRecordGapCenterValue - 89542,
    fullRecordGapCenterValue - 89422,
    fullRecordGapCenterValue - 89374,
    fullRecordGapCenterValue - 89100,
    fullRecordGapCenterValue - 89098,
    fullRecordGapCenterValue - 89014,
    fullRecordGapCenterValue - 88762,
    fullRecordGapCenterValue - 88704,
    fullRecordGapCenterValue - 88702,
    fullRecordGapCenterValue - 88498,
    fullRecordGapCenterValue - 88414,
    fullRecordGapCenterValue - 88402,
    fullRecordGapCenterValue - 88342,
    fullRecordGapCenterValue - 88042]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00056_fermat : ∀ n ∈ fullRecordGapRow00056_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03521_not_prime : ¬(recordGapCenter - 95962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95962]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03522_not_prime : ¬(recordGapCenter - 95878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95878]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03523_not_prime : ¬(recordGapCenter - 95554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95554]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03524_not_prime : ¬(recordGapCenter - 95482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95482]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03525_not_prime : ¬(recordGapCenter - 95434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95434]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03526_not_prime : ¬(recordGapCenter - 95422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95422]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03527_not_prime : ¬(recordGapCenter - 95398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95398]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03528_not_prime : ¬(recordGapCenter - 95218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95218]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03529_not_prime : ¬(recordGapCenter - 94918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94918]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03530_not_prime : ¬(recordGapCenter - 94864).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94864]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03531_not_prime : ¬(recordGapCenter - 94762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94762]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03532_not_prime : ¬(recordGapCenter - 94702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94702]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03533_not_prime : ¬(recordGapCenter - 94678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94678]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03534_not_prime : ¬(recordGapCenter - 94500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94500]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03535_not_prime : ¬(recordGapCenter - 94474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94474]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03536_not_prime : ¬(recordGapCenter - 94258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94258]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03537_not_prime : ¬(recordGapCenter - 93994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93994]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03538_not_prime : ¬(recordGapCenter - 93838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93838]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03539_not_prime : ¬(recordGapCenter - 93778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93778]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03540_not_prime : ¬(recordGapCenter - 93634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93634]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03541_not_prime : ¬(recordGapCenter - 93538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93538]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03542_not_prime : ¬(recordGapCenter - 93358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93358]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03543_not_prime : ¬(recordGapCenter - 93312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93312]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03544_not_prime : ¬(recordGapCenter - 93202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93202]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03545_not_prime : ¬(recordGapCenter - 93022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93022]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03546_not_prime : ¬(recordGapCenter - 92914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92914]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03547_not_prime : ¬(recordGapCenter - 92698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92698]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03548_not_prime : ¬(recordGapCenter - 92614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92614]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03549_not_prime : ¬(recordGapCenter - 92398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92398]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03550_not_prime : ¬(recordGapCenter - 92374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92374]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03551_not_prime : ¬(recordGapCenter - 92182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92182]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03552_not_prime : ¬(recordGapCenter - 92160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92160]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03553_not_prime : ¬(recordGapCenter - 92098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92098]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03554_not_prime : ¬(recordGapCenter - 91774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 91774]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03555_not_prime : ¬(recordGapCenter - 91738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 91738]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03556_not_prime : ¬(recordGapCenter - 91654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 91654]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03557_not_prime : ¬(recordGapCenter - 91534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 91534]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03558_not_prime : ¬(recordGapCenter - 91138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 91138]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03559_not_prime : ¬(recordGapCenter - 91114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 91114]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03560_not_prime : ¬(recordGapCenter - 90778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90778]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03561_not_prime : ¬(recordGapCenter - 90720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90720]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03562_not_prime : ¬(recordGapCenter - 90634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90634]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03563_not_prime : ¬(recordGapCenter - 90562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90562]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03564_not_prime : ¬(recordGapCenter - 90382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90382]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03565_not_prime : ¬(recordGapCenter - 90274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90274]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03566_not_prime : ¬(recordGapCenter - 90262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90262]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03567_not_prime : ¬(recordGapCenter - 89878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89878]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03568_not_prime : ¬(recordGapCenter - 89758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89758]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03569_not_prime : ¬(recordGapCenter - 89638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89638]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03570_not_prime : ¬(recordGapCenter - 89578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89578]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03571_not_prime : ¬(recordGapCenter - 89542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89542]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03572_not_prime : ¬(recordGapCenter - 89422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89422]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03573_not_prime : ¬(recordGapCenter - 89374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89374]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03574_not_prime : ¬(recordGapCenter - 89100).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89100]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03575_not_prime : ¬(recordGapCenter - 89098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89098]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03576_not_prime : ¬(recordGapCenter - 89014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89014]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03577_not_prime : ¬(recordGapCenter - 88762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88762]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03578_not_prime : ¬(recordGapCenter - 88704).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88704]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03579_not_prime : ¬(recordGapCenter - 88702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88702]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03580_not_prime : ¬(recordGapCenter - 88498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88498]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03581_not_prime : ¬(recordGapCenter - 88414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88414]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03582_not_prime : ¬(recordGapCenter - 88402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88402]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03583_not_prime : ¬(recordGapCenter - 88342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88342]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

theorem fullRecordGapTerm03584_not_prime : ¬(recordGapCenter - 88042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88042]
  · apply fullRecordGapRow00056_fermat
    simp [fullRecordGapRow00056_values]

end PrimeFactorUnimodality
