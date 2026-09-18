import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00008_values : List Nat :=
  [fullRecordGapCenterValue - 420474,
    fullRecordGapCenterValue - 420388,
    fullRecordGapCenterValue - 420382,
    fullRecordGapCenterValue - 420262,
    fullRecordGapCenterValue - 420234,
    fullRecordGapCenterValue - 420088,
    fullRecordGapCenterValue - 420054,
    fullRecordGapCenterValue - 420018,
    fullRecordGapCenterValue - 420000,
    fullRecordGapCenterValue - 419982,
    fullRecordGapCenterValue - 419788,
    fullRecordGapCenterValue - 419674,
    fullRecordGapCenterValue - 419578,
    fullRecordGapCenterValue - 419464,
    fullRecordGapCenterValue - 419262,
    fullRecordGapCenterValue - 419194,
    fullRecordGapCenterValue - 419158,
    fullRecordGapCenterValue - 419142,
    fullRecordGapCenterValue - 419134,
    fullRecordGapCenterValue - 419092,
    fullRecordGapCenterValue - 419032,
    fullRecordGapCenterValue - 418974,
    fullRecordGapCenterValue - 418962,
    fullRecordGapCenterValue - 418942,
    fullRecordGapCenterValue - 418918,
    fullRecordGapCenterValue - 418732,
    fullRecordGapCenterValue - 418714,
    fullRecordGapCenterValue - 418504,
    fullRecordGapCenterValue - 418408,
    fullRecordGapCenterValue - 418402,
    fullRecordGapCenterValue - 418372,
    fullRecordGapCenterValue - 418108,
    fullRecordGapCenterValue - 418024,
    fullRecordGapCenterValue - 417892,
    fullRecordGapCenterValue - 417778,
    fullRecordGapCenterValue - 417598,
    fullRecordGapCenterValue - 417532,
    fullRecordGapCenterValue - 417442,
    fullRecordGapCenterValue - 417244,
    fullRecordGapCenterValue - 417022,
    fullRecordGapCenterValue - 416994,
    fullRecordGapCenterValue - 416824,
    fullRecordGapCenterValue - 416818,
    fullRecordGapCenterValue - 416758,
    fullRecordGapCenterValue - 416742,
    fullRecordGapCenterValue - 416562,
    fullRecordGapCenterValue - 416554,
    fullRecordGapCenterValue - 416434,
    fullRecordGapCenterValue - 416418,
    fullRecordGapCenterValue - 416334,
    fullRecordGapCenterValue - 416212,
    fullRecordGapCenterValue - 416022,
    fullRecordGapCenterValue - 415942,
    fullRecordGapCenterValue - 415924,
    fullRecordGapCenterValue - 415894,
    fullRecordGapCenterValue - 415800,
    fullRecordGapCenterValue - 415768,
    fullRecordGapCenterValue - 415594,
    fullRecordGapCenterValue - 415468,
    fullRecordGapCenterValue - 415434,
    fullRecordGapCenterValue - 415432,
    fullRecordGapCenterValue - 415258,
    fullRecordGapCenterValue - 415204,
    fullRecordGapCenterValue - 414978]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00008_fermat : ∀ n ∈ fullRecordGapRow00008_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm00449_not_prime : ¬(recordGapCenter - 420474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420474]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00450_not_prime : ¬(recordGapCenter - 420388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420388]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00451_not_prime : ¬(recordGapCenter - 420382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420382]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00452_not_prime : ¬(recordGapCenter - 420262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420262]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00453_not_prime : ¬(recordGapCenter - 420234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420234]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00454_not_prime : ¬(recordGapCenter - 420088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420088]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00455_not_prime : ¬(recordGapCenter - 420054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420054]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00456_not_prime : ¬(recordGapCenter - 420018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420018]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00457_not_prime : ¬(recordGapCenter - 420000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 420000]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00458_not_prime : ¬(recordGapCenter - 419982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419982]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00459_not_prime : ¬(recordGapCenter - 419788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419788]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00460_not_prime : ¬(recordGapCenter - 419674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419674]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00461_not_prime : ¬(recordGapCenter - 419578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419578]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00462_not_prime : ¬(recordGapCenter - 419464).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419464]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00463_not_prime : ¬(recordGapCenter - 419262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419262]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00464_not_prime : ¬(recordGapCenter - 419194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419194]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00465_not_prime : ¬(recordGapCenter - 419158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419158]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00466_not_prime : ¬(recordGapCenter - 419142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419142]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00467_not_prime : ¬(recordGapCenter - 419134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419134]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00468_not_prime : ¬(recordGapCenter - 419092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419092]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00469_not_prime : ¬(recordGapCenter - 419032).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 419032]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00470_not_prime : ¬(recordGapCenter - 418974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418974]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00471_not_prime : ¬(recordGapCenter - 418962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418962]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00472_not_prime : ¬(recordGapCenter - 418942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418942]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00473_not_prime : ¬(recordGapCenter - 418918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418918]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00474_not_prime : ¬(recordGapCenter - 418732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418732]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00475_not_prime : ¬(recordGapCenter - 418714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418714]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00476_not_prime : ¬(recordGapCenter - 418504).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418504]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00477_not_prime : ¬(recordGapCenter - 418408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418408]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00478_not_prime : ¬(recordGapCenter - 418402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418402]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00479_not_prime : ¬(recordGapCenter - 418372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418372]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00480_not_prime : ¬(recordGapCenter - 418108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418108]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00481_not_prime : ¬(recordGapCenter - 418024).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 418024]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00482_not_prime : ¬(recordGapCenter - 417892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 417892]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00483_not_prime : ¬(recordGapCenter - 417778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 417778]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00484_not_prime : ¬(recordGapCenter - 417598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 417598]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00485_not_prime : ¬(recordGapCenter - 417532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 417532]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00486_not_prime : ¬(recordGapCenter - 417442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 417442]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00487_not_prime : ¬(recordGapCenter - 417244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 417244]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00488_not_prime : ¬(recordGapCenter - 417022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 417022]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00489_not_prime : ¬(recordGapCenter - 416994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416994]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00490_not_prime : ¬(recordGapCenter - 416824).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416824]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00491_not_prime : ¬(recordGapCenter - 416818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416818]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00492_not_prime : ¬(recordGapCenter - 416758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416758]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00493_not_prime : ¬(recordGapCenter - 416742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416742]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00494_not_prime : ¬(recordGapCenter - 416562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416562]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00495_not_prime : ¬(recordGapCenter - 416554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416554]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00496_not_prime : ¬(recordGapCenter - 416434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416434]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00497_not_prime : ¬(recordGapCenter - 416418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416418]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00498_not_prime : ¬(recordGapCenter - 416334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416334]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00499_not_prime : ¬(recordGapCenter - 416212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416212]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00500_not_prime : ¬(recordGapCenter - 416022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 416022]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00501_not_prime : ¬(recordGapCenter - 415942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415942]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00502_not_prime : ¬(recordGapCenter - 415924).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415924]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00503_not_prime : ¬(recordGapCenter - 415894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415894]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00504_not_prime : ¬(recordGapCenter - 415800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415800]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00505_not_prime : ¬(recordGapCenter - 415768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415768]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00506_not_prime : ¬(recordGapCenter - 415594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415594]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00507_not_prime : ¬(recordGapCenter - 415468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415468]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00508_not_prime : ¬(recordGapCenter - 415434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415434]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00509_not_prime : ¬(recordGapCenter - 415432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415432]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00510_not_prime : ¬(recordGapCenter - 415258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415258]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00511_not_prime : ¬(recordGapCenter - 415204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 415204]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

theorem fullRecordGapTerm00512_not_prime : ¬(recordGapCenter - 414978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 414978]
  · apply fullRecordGapRow00008_fermat
    simp [fullRecordGapRow00008_values]

end PrimeFactorUnimodality
