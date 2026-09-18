import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00075_values : List Nat :=
  [fullRecordGapCenterValue + 193958,
    fullRecordGapCenterValue + 194006,
    fullRecordGapCenterValue + 194042,
    fullRecordGapCenterValue + 194108,
    fullRecordGapCenterValue + 194156,
    fullRecordGapCenterValue + 194162,
    fullRecordGapCenterValue + 194252,
    fullRecordGapCenterValue + 194318,
    fullRecordGapCenterValue + 194342,
    fullRecordGapCenterValue + 194372,
    fullRecordGapCenterValue + 194400,
    fullRecordGapCenterValue + 194462,
    fullRecordGapCenterValue + 194588,
    fullRecordGapCenterValue + 194846,
    fullRecordGapCenterValue + 194882,
    fullRecordGapCenterValue + 194906,
    fullRecordGapCenterValue + 195122,
    fullRecordGapCenterValue + 195218,
    fullRecordGapCenterValue + 195302,
    fullRecordGapCenterValue + 195428,
    fullRecordGapCenterValue + 195458,
    fullRecordGapCenterValue + 195542,
    fullRecordGapCenterValue + 196022,
    fullRecordGapCenterValue + 196436,
    fullRecordGapCenterValue + 196502,
    fullRecordGapCenterValue + 196556,
    fullRecordGapCenterValue + 196628,
    fullRecordGapCenterValue + 196646,
    fullRecordGapCenterValue + 196778,
    fullRecordGapCenterValue + 196796,
    fullRecordGapCenterValue + 196886,
    fullRecordGapCenterValue + 196892,
    fullRecordGapCenterValue + 196982,
    fullRecordGapCenterValue + 197108,
    fullRecordGapCenterValue + 197120,
    fullRecordGapCenterValue + 197426,
    fullRecordGapCenterValue + 197558,
    fullRecordGapCenterValue + 197822,
    fullRecordGapCenterValue + 197852,
    fullRecordGapCenterValue + 197906,
    fullRecordGapCenterValue + 198026,
    fullRecordGapCenterValue + 198236,
    fullRecordGapCenterValue + 198362,
    fullRecordGapCenterValue + 198446,
    fullRecordGapCenterValue + 198452,
    fullRecordGapCenterValue + 198482,
    fullRecordGapCenterValue + 198518,
    fullRecordGapCenterValue + 198578,
    fullRecordGapCenterValue + 198668,
    fullRecordGapCenterValue + 198698,
    fullRecordGapCenterValue + 198878,
    fullRecordGapCenterValue + 198908,
    fullRecordGapCenterValue + 199028,
    fullRecordGapCenterValue + 199046,
    fullRecordGapCenterValue + 199148,
    fullRecordGapCenterValue + 199322,
    fullRecordGapCenterValue + 199412,
    fullRecordGapCenterValue + 199466,
    fullRecordGapCenterValue + 199508,
    fullRecordGapCenterValue + 199586,
    fullRecordGapCenterValue + 199658,
    fullRecordGapCenterValue + 199748,
    fullRecordGapCenterValue + 200132,
    fullRecordGapCenterValue + 200348]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00075_fermat : ∀ n ∈ fullRecordGapRow00075_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04737_not_prime : ¬(recordGapCenter + 193958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 193958]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04738_not_prime : ¬(recordGapCenter + 194006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194006]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04739_not_prime : ¬(recordGapCenter + 194042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194042]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04740_not_prime : ¬(recordGapCenter + 194108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194108]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04741_not_prime : ¬(recordGapCenter + 194156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194156]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04742_not_prime : ¬(recordGapCenter + 194162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194162]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04743_not_prime : ¬(recordGapCenter + 194252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194252]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04744_not_prime : ¬(recordGapCenter + 194318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194318]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04745_not_prime : ¬(recordGapCenter + 194342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194342]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04746_not_prime : ¬(recordGapCenter + 194372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194372]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04747_not_prime : ¬(recordGapCenter + 194400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194400]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04748_not_prime : ¬(recordGapCenter + 194462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194462]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04749_not_prime : ¬(recordGapCenter + 194588).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194588]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04750_not_prime : ¬(recordGapCenter + 194846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194846]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04751_not_prime : ¬(recordGapCenter + 194882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194882]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04752_not_prime : ¬(recordGapCenter + 194906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 194906]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04753_not_prime : ¬(recordGapCenter + 195122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 195122]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04754_not_prime : ¬(recordGapCenter + 195218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 195218]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04755_not_prime : ¬(recordGapCenter + 195302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 195302]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04756_not_prime : ¬(recordGapCenter + 195428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 195428]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04757_not_prime : ¬(recordGapCenter + 195458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 195458]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04758_not_prime : ¬(recordGapCenter + 195542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 195542]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04759_not_prime : ¬(recordGapCenter + 196022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 196022]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04760_not_prime : ¬(recordGapCenter + 196436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 196436]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04761_not_prime : ¬(recordGapCenter + 196502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 196502]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04762_not_prime : ¬(recordGapCenter + 196556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 196556]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04763_not_prime : ¬(recordGapCenter + 196628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 196628]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04764_not_prime : ¬(recordGapCenter + 196646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 196646]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04765_not_prime : ¬(recordGapCenter + 196778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 196778]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04766_not_prime : ¬(recordGapCenter + 196796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 196796]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04767_not_prime : ¬(recordGapCenter + 196886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 196886]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04768_not_prime : ¬(recordGapCenter + 196892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 196892]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04769_not_prime : ¬(recordGapCenter + 196982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 196982]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04770_not_prime : ¬(recordGapCenter + 197108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 197108]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04771_not_prime : ¬(recordGapCenter + 197120).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 197120]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04772_not_prime : ¬(recordGapCenter + 197426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 197426]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04773_not_prime : ¬(recordGapCenter + 197558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 197558]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04774_not_prime : ¬(recordGapCenter + 197822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 197822]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04775_not_prime : ¬(recordGapCenter + 197852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 197852]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04776_not_prime : ¬(recordGapCenter + 197906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 197906]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04777_not_prime : ¬(recordGapCenter + 198026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 198026]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04778_not_prime : ¬(recordGapCenter + 198236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 198236]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04779_not_prime : ¬(recordGapCenter + 198362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 198362]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04780_not_prime : ¬(recordGapCenter + 198446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 198446]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04781_not_prime : ¬(recordGapCenter + 198452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 198452]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04782_not_prime : ¬(recordGapCenter + 198482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 198482]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04783_not_prime : ¬(recordGapCenter + 198518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 198518]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04784_not_prime : ¬(recordGapCenter + 198578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 198578]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04785_not_prime : ¬(recordGapCenter + 198668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 198668]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04786_not_prime : ¬(recordGapCenter + 198698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 198698]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04787_not_prime : ¬(recordGapCenter + 198878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 198878]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04788_not_prime : ¬(recordGapCenter + 198908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 198908]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04789_not_prime : ¬(recordGapCenter + 199028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 199028]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04790_not_prime : ¬(recordGapCenter + 199046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 199046]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04791_not_prime : ¬(recordGapCenter + 199148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 199148]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04792_not_prime : ¬(recordGapCenter + 199322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 199322]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04793_not_prime : ¬(recordGapCenter + 199412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 199412]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04794_not_prime : ¬(recordGapCenter + 199466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 199466]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04795_not_prime : ¬(recordGapCenter + 199508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 199508]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04796_not_prime : ¬(recordGapCenter + 199586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 199586]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04797_not_prime : ¬(recordGapCenter + 199658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 199658]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04798_not_prime : ¬(recordGapCenter + 199748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 199748]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04799_not_prime : ¬(recordGapCenter + 200132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 200132]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

theorem fullRecordGapTerm04800_not_prime : ¬(recordGapCenter + 200348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 200348]
  · apply fullRecordGapRow00075_fermat
    simp [fullRecordGapRow00075_values]

end PrimeFactorUnimodality
