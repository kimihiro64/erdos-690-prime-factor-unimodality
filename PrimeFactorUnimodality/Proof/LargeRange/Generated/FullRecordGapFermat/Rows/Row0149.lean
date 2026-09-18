import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00149_values : List Nat :=
  [fullRecordGapCenterValue + 568572,
    fullRecordGapCenterValue + 568892,
    fullRecordGapCenterValue + 568970,
    fullRecordGapCenterValue + 569018,
    fullRecordGapCenterValue + 569046,
    fullRecordGapCenterValue + 569090,
    fullRecordGapCenterValue + 569172,
    fullRecordGapCenterValue + 569186,
    fullRecordGapCenterValue + 569210,
    fullRecordGapCenterValue + 569276,
    fullRecordGapCenterValue + 569318,
    fullRecordGapCenterValue + 569336,
    fullRecordGapCenterValue + 569508,
    fullRecordGapCenterValue + 569528,
    fullRecordGapCenterValue + 569570,
    fullRecordGapCenterValue + 569612,
    fullRecordGapCenterValue + 569630,
    fullRecordGapCenterValue + 569678,
    fullRecordGapCenterValue + 569706,
    fullRecordGapCenterValue + 569732,
    fullRecordGapCenterValue + 569762,
    fullRecordGapCenterValue + 569958,
    fullRecordGapCenterValue + 569978,
    fullRecordGapCenterValue + 569990,
    fullRecordGapCenterValue + 570012,
    fullRecordGapCenterValue + 570098,
    fullRecordGapCenterValue + 570242,
    fullRecordGapCenterValue + 570252,
    fullRecordGapCenterValue + 570278,
    fullRecordGapCenterValue + 570356,
    fullRecordGapCenterValue + 570428,
    fullRecordGapCenterValue + 570470,
    fullRecordGapCenterValue + 570476,
    fullRecordGapCenterValue + 570498,
    fullRecordGapCenterValue + 570516,
    fullRecordGapCenterValue + 570558,
    fullRecordGapCenterValue + 570666,
    fullRecordGapCenterValue + 570692,
    fullRecordGapCenterValue + 570756,
    fullRecordGapCenterValue + 570770,
    fullRecordGapCenterValue + 570858,
    fullRecordGapCenterValue + 570890,
    fullRecordGapCenterValue + 571070,
    fullRecordGapCenterValue + 571092,
    fullRecordGapCenterValue + 571112,
    fullRecordGapCenterValue + 571146,
    fullRecordGapCenterValue + 571148,
    fullRecordGapCenterValue + 571190,
    fullRecordGapCenterValue + 571196,
    fullRecordGapCenterValue + 571218,
    fullRecordGapCenterValue + 571278,
    fullRecordGapCenterValue + 571308,
    fullRecordGapCenterValue + 571322,
    fullRecordGapCenterValue + 571386,
    fullRecordGapCenterValue + 571398,
    fullRecordGapCenterValue + 571476,
    fullRecordGapCenterValue + 571496,
    fullRecordGapCenterValue + 571646,
    fullRecordGapCenterValue + 571730,
    fullRecordGapCenterValue + 571832,
    fullRecordGapCenterValue + 571866,
    fullRecordGapCenterValue + 571902,
    fullRecordGapCenterValue + 571916,
    fullRecordGapCenterValue + 571958]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00149_fermat : ∀ n ∈ fullRecordGapRow00149_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09473_not_prime : ¬(recordGapCenter + 568572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 568572]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09474_not_prime : ¬(recordGapCenter + 568892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 568892]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09475_not_prime : ¬(recordGapCenter + 568970).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 568970]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09476_not_prime : ¬(recordGapCenter + 569018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569018]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09477_not_prime : ¬(recordGapCenter + 569046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569046]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09478_not_prime : ¬(recordGapCenter + 569090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569090]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09479_not_prime : ¬(recordGapCenter + 569172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569172]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09480_not_prime : ¬(recordGapCenter + 569186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569186]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09481_not_prime : ¬(recordGapCenter + 569210).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569210]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09482_not_prime : ¬(recordGapCenter + 569276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569276]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09483_not_prime : ¬(recordGapCenter + 569318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569318]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09484_not_prime : ¬(recordGapCenter + 569336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569336]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09485_not_prime : ¬(recordGapCenter + 569508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569508]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09486_not_prime : ¬(recordGapCenter + 569528).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569528]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09487_not_prime : ¬(recordGapCenter + 569570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569570]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09488_not_prime : ¬(recordGapCenter + 569612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569612]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09489_not_prime : ¬(recordGapCenter + 569630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569630]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09490_not_prime : ¬(recordGapCenter + 569678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569678]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09491_not_prime : ¬(recordGapCenter + 569706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569706]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09492_not_prime : ¬(recordGapCenter + 569732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569732]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09493_not_prime : ¬(recordGapCenter + 569762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569762]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09494_not_prime : ¬(recordGapCenter + 569958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569958]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09495_not_prime : ¬(recordGapCenter + 569978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569978]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09496_not_prime : ¬(recordGapCenter + 569990).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 569990]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09497_not_prime : ¬(recordGapCenter + 570012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570012]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09498_not_prime : ¬(recordGapCenter + 570098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570098]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09499_not_prime : ¬(recordGapCenter + 570242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570242]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09500_not_prime : ¬(recordGapCenter + 570252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570252]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09501_not_prime : ¬(recordGapCenter + 570278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570278]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09502_not_prime : ¬(recordGapCenter + 570356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570356]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09503_not_prime : ¬(recordGapCenter + 570428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570428]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09504_not_prime : ¬(recordGapCenter + 570470).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570470]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09505_not_prime : ¬(recordGapCenter + 570476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570476]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09506_not_prime : ¬(recordGapCenter + 570498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570498]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09507_not_prime : ¬(recordGapCenter + 570516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570516]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09508_not_prime : ¬(recordGapCenter + 570558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570558]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09509_not_prime : ¬(recordGapCenter + 570666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570666]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09510_not_prime : ¬(recordGapCenter + 570692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570692]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09511_not_prime : ¬(recordGapCenter + 570756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570756]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09512_not_prime : ¬(recordGapCenter + 570770).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570770]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09513_not_prime : ¬(recordGapCenter + 570858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570858]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09514_not_prime : ¬(recordGapCenter + 570890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 570890]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09515_not_prime : ¬(recordGapCenter + 571070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571070]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09516_not_prime : ¬(recordGapCenter + 571092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571092]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09517_not_prime : ¬(recordGapCenter + 571112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571112]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09518_not_prime : ¬(recordGapCenter + 571146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571146]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09519_not_prime : ¬(recordGapCenter + 571148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571148]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09520_not_prime : ¬(recordGapCenter + 571190).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571190]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09521_not_prime : ¬(recordGapCenter + 571196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571196]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09522_not_prime : ¬(recordGapCenter + 571218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571218]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09523_not_prime : ¬(recordGapCenter + 571278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571278]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09524_not_prime : ¬(recordGapCenter + 571308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571308]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09525_not_prime : ¬(recordGapCenter + 571322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571322]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09526_not_prime : ¬(recordGapCenter + 571386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571386]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09527_not_prime : ¬(recordGapCenter + 571398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571398]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09528_not_prime : ¬(recordGapCenter + 571476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571476]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09529_not_prime : ¬(recordGapCenter + 571496).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571496]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09530_not_prime : ¬(recordGapCenter + 571646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571646]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09531_not_prime : ¬(recordGapCenter + 571730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571730]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09532_not_prime : ¬(recordGapCenter + 571832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571832]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09533_not_prime : ¬(recordGapCenter + 571866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571866]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09534_not_prime : ¬(recordGapCenter + 571902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571902]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09535_not_prime : ¬(recordGapCenter + 571916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571916]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

theorem fullRecordGapTerm09536_not_prime : ¬(recordGapCenter + 571958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 571958]
  · apply fullRecordGapRow00149_fermat
    simp [fullRecordGapRow00149_values]

end PrimeFactorUnimodality
