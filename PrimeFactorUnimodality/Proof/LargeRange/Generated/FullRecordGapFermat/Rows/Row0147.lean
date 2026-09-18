import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00147_values : List Nat :=
  [fullRecordGapCenterValue + 559956,
    fullRecordGapCenterValue + 559970,
    fullRecordGapCenterValue + 559976,
    fullRecordGapCenterValue + 560000,
    fullRecordGapCenterValue + 560018,
    fullRecordGapCenterValue + 560022,
    fullRecordGapCenterValue + 560036,
    fullRecordGapCenterValue + 560148,
    fullRecordGapCenterValue + 560198,
    fullRecordGapCenterValue + 560262,
    fullRecordGapCenterValue + 560298,
    fullRecordGapCenterValue + 560366,
    fullRecordGapCenterValue + 560390,
    fullRecordGapCenterValue + 560408,
    fullRecordGapCenterValue + 560436,
    fullRecordGapCenterValue + 560442,
    fullRecordGapCenterValue + 560486,
    fullRecordGapCenterValue + 560562,
    fullRecordGapCenterValue + 560606,
    fullRecordGapCenterValue + 560642,
    fullRecordGapCenterValue + 560702,
    fullRecordGapCenterValue + 560708,
    fullRecordGapCenterValue + 560792,
    fullRecordGapCenterValue + 560828,
    fullRecordGapCenterValue + 560870,
    fullRecordGapCenterValue + 560990,
    fullRecordGapCenterValue + 561026,
    fullRecordGapCenterValue + 561122,
    fullRecordGapCenterValue + 561188,
    fullRecordGapCenterValue + 561230,
    fullRecordGapCenterValue + 561330,
    fullRecordGapCenterValue + 561356,
    fullRecordGapCenterValue + 561398,
    fullRecordGapCenterValue + 561422,
    fullRecordGapCenterValue + 561452,
    fullRecordGapCenterValue + 561486,
    fullRecordGapCenterValue + 561542,
    fullRecordGapCenterValue + 561606,
    fullRecordGapCenterValue + 561642,
    fullRecordGapCenterValue + 561692,
    fullRecordGapCenterValue + 561732,
    fullRecordGapCenterValue + 561842,
    fullRecordGapCenterValue + 561908,
    fullRecordGapCenterValue + 561948,
    fullRecordGapCenterValue + 562046,
    fullRecordGapCenterValue + 562370,
    fullRecordGapCenterValue + 562376,
    fullRecordGapCenterValue + 562412,
    fullRecordGapCenterValue + 562500,
    fullRecordGapCenterValue + 562502,
    fullRecordGapCenterValue + 562556,
    fullRecordGapCenterValue + 562808,
    fullRecordGapCenterValue + 562962,
    fullRecordGapCenterValue + 563018,
    fullRecordGapCenterValue + 563048,
    fullRecordGapCenterValue + 563102,
    fullRecordGapCenterValue + 563126,
    fullRecordGapCenterValue + 563252,
    fullRecordGapCenterValue + 563348,
    fullRecordGapCenterValue + 563522,
    fullRecordGapCenterValue + 563538,
    fullRecordGapCenterValue + 563606,
    fullRecordGapCenterValue + 563846,
    fullRecordGapCenterValue + 563942]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00147_fermat : ∀ n ∈ fullRecordGapRow00147_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm09345_not_prime : ¬(recordGapCenter + 559956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559956]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09346_not_prime : ¬(recordGapCenter + 559970).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559970]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09347_not_prime : ¬(recordGapCenter + 559976).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 559976]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09348_not_prime : ¬(recordGapCenter + 560000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560000]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09349_not_prime : ¬(recordGapCenter + 560018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560018]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09350_not_prime : ¬(recordGapCenter + 560022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560022]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09351_not_prime : ¬(recordGapCenter + 560036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560036]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09352_not_prime : ¬(recordGapCenter + 560148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560148]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09353_not_prime : ¬(recordGapCenter + 560198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560198]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09354_not_prime : ¬(recordGapCenter + 560262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560262]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09355_not_prime : ¬(recordGapCenter + 560298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560298]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09356_not_prime : ¬(recordGapCenter + 560366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560366]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09357_not_prime : ¬(recordGapCenter + 560390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560390]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09358_not_prime : ¬(recordGapCenter + 560408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560408]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09359_not_prime : ¬(recordGapCenter + 560436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560436]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09360_not_prime : ¬(recordGapCenter + 560442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560442]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09361_not_prime : ¬(recordGapCenter + 560486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560486]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09362_not_prime : ¬(recordGapCenter + 560562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560562]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09363_not_prime : ¬(recordGapCenter + 560606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560606]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09364_not_prime : ¬(recordGapCenter + 560642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560642]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09365_not_prime : ¬(recordGapCenter + 560702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560702]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09366_not_prime : ¬(recordGapCenter + 560708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560708]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09367_not_prime : ¬(recordGapCenter + 560792).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560792]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09368_not_prime : ¬(recordGapCenter + 560828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560828]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09369_not_prime : ¬(recordGapCenter + 560870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560870]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09370_not_prime : ¬(recordGapCenter + 560990).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 560990]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09371_not_prime : ¬(recordGapCenter + 561026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561026]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09372_not_prime : ¬(recordGapCenter + 561122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561122]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09373_not_prime : ¬(recordGapCenter + 561188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561188]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09374_not_prime : ¬(recordGapCenter + 561230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561230]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09375_not_prime : ¬(recordGapCenter + 561330).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561330]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09376_not_prime : ¬(recordGapCenter + 561356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561356]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09377_not_prime : ¬(recordGapCenter + 561398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561398]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09378_not_prime : ¬(recordGapCenter + 561422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561422]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09379_not_prime : ¬(recordGapCenter + 561452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561452]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09380_not_prime : ¬(recordGapCenter + 561486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561486]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09381_not_prime : ¬(recordGapCenter + 561542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561542]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09382_not_prime : ¬(recordGapCenter + 561606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561606]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09383_not_prime : ¬(recordGapCenter + 561642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561642]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09384_not_prime : ¬(recordGapCenter + 561692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561692]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09385_not_prime : ¬(recordGapCenter + 561732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561732]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09386_not_prime : ¬(recordGapCenter + 561842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561842]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09387_not_prime : ¬(recordGapCenter + 561908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561908]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09388_not_prime : ¬(recordGapCenter + 561948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 561948]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09389_not_prime : ¬(recordGapCenter + 562046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 562046]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09390_not_prime : ¬(recordGapCenter + 562370).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 562370]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09391_not_prime : ¬(recordGapCenter + 562376).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 562376]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09392_not_prime : ¬(recordGapCenter + 562412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 562412]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09393_not_prime : ¬(recordGapCenter + 562500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 562500]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09394_not_prime : ¬(recordGapCenter + 562502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 562502]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09395_not_prime : ¬(recordGapCenter + 562556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 562556]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09396_not_prime : ¬(recordGapCenter + 562808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 562808]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09397_not_prime : ¬(recordGapCenter + 562962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 562962]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09398_not_prime : ¬(recordGapCenter + 563018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 563018]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09399_not_prime : ¬(recordGapCenter + 563048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 563048]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09400_not_prime : ¬(recordGapCenter + 563102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 563102]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09401_not_prime : ¬(recordGapCenter + 563126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 563126]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09402_not_prime : ¬(recordGapCenter + 563252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 563252]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09403_not_prime : ¬(recordGapCenter + 563348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 563348]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09404_not_prime : ¬(recordGapCenter + 563522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 563522]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09405_not_prime : ¬(recordGapCenter + 563538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 563538]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09406_not_prime : ¬(recordGapCenter + 563606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 563606]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09407_not_prime : ¬(recordGapCenter + 563846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 563846]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

theorem fullRecordGapTerm09408_not_prime : ¬(recordGapCenter + 563942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 563942]
  · apply fullRecordGapRow00147_fermat
    simp [fullRecordGapRow00147_values]

end PrimeFactorUnimodality
