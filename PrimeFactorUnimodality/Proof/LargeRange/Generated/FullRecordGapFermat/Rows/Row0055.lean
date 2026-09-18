import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00055_values : List Nat :=
  [fullRecordGapCenterValue - 106294,
    fullRecordGapCenterValue - 106258,
    fullRecordGapCenterValue - 106234,
    fullRecordGapCenterValue - 106174,
    fullRecordGapCenterValue - 106102,
    fullRecordGapCenterValue - 105838,
    fullRecordGapCenterValue - 105454,
    fullRecordGapCenterValue - 105394,
    fullRecordGapCenterValue - 105082,
    fullRecordGapCenterValue - 105058,
    fullRecordGapCenterValue - 104722,
    fullRecordGapCenterValue - 104544,
    fullRecordGapCenterValue - 104362,
    fullRecordGapCenterValue - 103858,
    fullRecordGapCenterValue - 103498,
    fullRecordGapCenterValue - 103488,
    fullRecordGapCenterValue - 103438,
    fullRecordGapCenterValue - 103078,
    fullRecordGapCenterValue - 102958,
    fullRecordGapCenterValue - 102874,
    fullRecordGapCenterValue - 102694,
    fullRecordGapCenterValue - 102658,
    fullRecordGapCenterValue - 102514,
    fullRecordGapCenterValue - 102478,
    fullRecordGapCenterValue - 102262,
    fullRecordGapCenterValue - 102142,
    fullRecordGapCenterValue - 102118,
    fullRecordGapCenterValue - 102094,
    fullRecordGapCenterValue - 102060,
    fullRecordGapCenterValue - 101302,
    fullRecordGapCenterValue - 101254,
    fullRecordGapCenterValue - 101250,
    fullRecordGapCenterValue - 101098,
    fullRecordGapCenterValue - 100834,
    fullRecordGapCenterValue - 100774,
    fullRecordGapCenterValue - 100222,
    fullRecordGapCenterValue - 100174,
    fullRecordGapCenterValue - 100000,
    fullRecordGapCenterValue - 99874,
    fullRecordGapCenterValue - 99754,
    fullRecordGapCenterValue - 99742,
    fullRecordGapCenterValue - 99622,
    fullRecordGapCenterValue - 99574,
    fullRecordGapCenterValue - 99454,
    fullRecordGapCenterValue - 99000,
    fullRecordGapCenterValue - 98962,
    fullRecordGapCenterValue - 98818,
    fullRecordGapCenterValue - 98662,
    fullRecordGapCenterValue - 98614,
    fullRecordGapCenterValue - 98422,
    fullRecordGapCenterValue - 98314,
    fullRecordGapCenterValue - 98304,
    fullRecordGapCenterValue - 98074,
    fullRecordGapCenterValue - 98062,
    fullRecordGapCenterValue - 97738,
    fullRecordGapCenterValue - 97558,
    fullRecordGapCenterValue - 97054,
    fullRecordGapCenterValue - 97020,
    fullRecordGapCenterValue - 96898,
    fullRecordGapCenterValue - 96682,
    fullRecordGapCenterValue - 96598,
    fullRecordGapCenterValue - 96394,
    fullRecordGapCenterValue - 96228,
    fullRecordGapCenterValue - 96000]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00055_fermat : ∀ n ∈ fullRecordGapRow00055_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03457_not_prime : ¬(recordGapCenter - 106294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106294]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03458_not_prime : ¬(recordGapCenter - 106258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106258]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03459_not_prime : ¬(recordGapCenter - 106234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106234]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03460_not_prime : ¬(recordGapCenter - 106174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106174]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03461_not_prime : ¬(recordGapCenter - 106102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106102]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03462_not_prime : ¬(recordGapCenter - 105838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 105838]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03463_not_prime : ¬(recordGapCenter - 105454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 105454]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03464_not_prime : ¬(recordGapCenter - 105394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 105394]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03465_not_prime : ¬(recordGapCenter - 105082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 105082]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03466_not_prime : ¬(recordGapCenter - 105058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 105058]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03467_not_prime : ¬(recordGapCenter - 104722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 104722]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03468_not_prime : ¬(recordGapCenter - 104544).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 104544]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03469_not_prime : ¬(recordGapCenter - 104362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 104362]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03470_not_prime : ¬(recordGapCenter - 103858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 103858]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03471_not_prime : ¬(recordGapCenter - 103498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 103498]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03472_not_prime : ¬(recordGapCenter - 103488).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 103488]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03473_not_prime : ¬(recordGapCenter - 103438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 103438]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03474_not_prime : ¬(recordGapCenter - 103078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 103078]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03475_not_prime : ¬(recordGapCenter - 102958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102958]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03476_not_prime : ¬(recordGapCenter - 102874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102874]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03477_not_prime : ¬(recordGapCenter - 102694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102694]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03478_not_prime : ¬(recordGapCenter - 102658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102658]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03479_not_prime : ¬(recordGapCenter - 102514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102514]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03480_not_prime : ¬(recordGapCenter - 102478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102478]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03481_not_prime : ¬(recordGapCenter - 102262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102262]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03482_not_prime : ¬(recordGapCenter - 102142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102142]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03483_not_prime : ¬(recordGapCenter - 102118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102118]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03484_not_prime : ¬(recordGapCenter - 102094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102094]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03485_not_prime : ¬(recordGapCenter - 102060).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102060]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03486_not_prime : ¬(recordGapCenter - 101302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 101302]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03487_not_prime : ¬(recordGapCenter - 101254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 101254]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03488_not_prime : ¬(recordGapCenter - 101250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 101250]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03489_not_prime : ¬(recordGapCenter - 101098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 101098]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03490_not_prime : ¬(recordGapCenter - 100834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 100834]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03491_not_prime : ¬(recordGapCenter - 100774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 100774]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03492_not_prime : ¬(recordGapCenter - 100222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 100222]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03493_not_prime : ¬(recordGapCenter - 100174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 100174]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03494_not_prime : ¬(recordGapCenter - 100000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 100000]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03495_not_prime : ¬(recordGapCenter - 99874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 99874]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03496_not_prime : ¬(recordGapCenter - 99754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 99754]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03497_not_prime : ¬(recordGapCenter - 99742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 99742]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03498_not_prime : ¬(recordGapCenter - 99622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 99622]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03499_not_prime : ¬(recordGapCenter - 99574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 99574]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03500_not_prime : ¬(recordGapCenter - 99454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 99454]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03501_not_prime : ¬(recordGapCenter - 99000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 99000]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03502_not_prime : ¬(recordGapCenter - 98962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98962]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03503_not_prime : ¬(recordGapCenter - 98818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98818]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03504_not_prime : ¬(recordGapCenter - 98662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98662]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03505_not_prime : ¬(recordGapCenter - 98614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98614]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03506_not_prime : ¬(recordGapCenter - 98422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98422]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03507_not_prime : ¬(recordGapCenter - 98314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98314]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03508_not_prime : ¬(recordGapCenter - 98304).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98304]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03509_not_prime : ¬(recordGapCenter - 98074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98074]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03510_not_prime : ¬(recordGapCenter - 98062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98062]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03511_not_prime : ¬(recordGapCenter - 97738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 97738]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03512_not_prime : ¬(recordGapCenter - 97558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 97558]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03513_not_prime : ¬(recordGapCenter - 97054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 97054]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03514_not_prime : ¬(recordGapCenter - 97020).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 97020]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03515_not_prime : ¬(recordGapCenter - 96898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 96898]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03516_not_prime : ¬(recordGapCenter - 96682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 96682]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03517_not_prime : ¬(recordGapCenter - 96598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 96598]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03518_not_prime : ¬(recordGapCenter - 96394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 96394]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03519_not_prime : ¬(recordGapCenter - 96228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 96228]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

theorem fullRecordGapTerm03520_not_prime : ¬(recordGapCenter - 96000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 96000]
  · apply fullRecordGapRow00055_fermat
    simp [fullRecordGapRow00055_values]

end PrimeFactorUnimodality
