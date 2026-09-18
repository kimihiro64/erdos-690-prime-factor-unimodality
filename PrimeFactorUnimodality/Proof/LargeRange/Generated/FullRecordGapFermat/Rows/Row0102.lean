import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00102_values : List Nat :=
  [fullRecordGapCenterValue + 353042,
    fullRecordGapCenterValue + 353048,
    fullRecordGapCenterValue + 353222,
    fullRecordGapCenterValue + 353348,
    fullRecordGapCenterValue + 353406,
    fullRecordGapCenterValue + 353442,
    fullRecordGapCenterValue + 353516,
    fullRecordGapCenterValue + 353658,
    fullRecordGapCenterValue + 353768,
    fullRecordGapCenterValue + 353876,
    fullRecordGapCenterValue + 353946,
    fullRecordGapCenterValue + 353966,
    fullRecordGapCenterValue + 353972,
    fullRecordGapCenterValue + 354092,
    fullRecordGapCenterValue + 354126,
    fullRecordGapCenterValue + 354182,
    fullRecordGapCenterValue + 354422,
    fullRecordGapCenterValue + 354446,
    fullRecordGapCenterValue + 354572,
    fullRecordGapCenterValue + 354758,
    fullRecordGapCenterValue + 354816,
    fullRecordGapCenterValue + 354842,
    fullRecordGapCenterValue + 354846,
    fullRecordGapCenterValue + 355002,
    fullRecordGapCenterValue + 355022,
    fullRecordGapCenterValue + 355182,
    fullRecordGapCenterValue + 355478,
    fullRecordGapCenterValue + 355526,
    fullRecordGapCenterValue + 355622,
    fullRecordGapCenterValue + 355638,
    fullRecordGapCenterValue + 355686,
    fullRecordGapCenterValue + 355766,
    fullRecordGapCenterValue + 355826,
    fullRecordGapCenterValue + 355988,
    fullRecordGapCenterValue + 356036,
    fullRecordGapCenterValue + 356042,
    fullRecordGapCenterValue + 356186,
    fullRecordGapCenterValue + 356228,
    fullRecordGapCenterValue + 356276,
    fullRecordGapCenterValue + 356322,
    fullRecordGapCenterValue + 356358,
    fullRecordGapCenterValue + 356492,
    fullRecordGapCenterValue + 356498,
    fullRecordGapCenterValue + 356666,
    fullRecordGapCenterValue + 356786,
    fullRecordGapCenterValue + 356802,
    fullRecordGapCenterValue + 356882,
    fullRecordGapCenterValue + 356948,
    fullRecordGapCenterValue + 356982,
    fullRecordGapCenterValue + 357002,
    fullRecordGapCenterValue + 357026,
    fullRecordGapCenterValue + 357092,
    fullRecordGapCenterValue + 357218,
    fullRecordGapCenterValue + 357242,
    fullRecordGapCenterValue + 357402,
    fullRecordGapCenterValue + 357548,
    fullRecordGapCenterValue + 357596,
    fullRecordGapCenterValue + 357662,
    fullRecordGapCenterValue + 357668,
    fullRecordGapCenterValue + 357726,
    fullRecordGapCenterValue + 357746,
    fullRecordGapCenterValue + 357806,
    fullRecordGapCenterValue + 357908,
    fullRecordGapCenterValue + 357978]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00102_fermat : ∀ n ∈ fullRecordGapRow00102_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06465_not_prime : ¬(recordGapCenter + 353042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353042]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06466_not_prime : ¬(recordGapCenter + 353048).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353048]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06467_not_prime : ¬(recordGapCenter + 353222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353222]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06468_not_prime : ¬(recordGapCenter + 353348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353348]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06469_not_prime : ¬(recordGapCenter + 353406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353406]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06470_not_prime : ¬(recordGapCenter + 353442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353442]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06471_not_prime : ¬(recordGapCenter + 353516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353516]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06472_not_prime : ¬(recordGapCenter + 353658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353658]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06473_not_prime : ¬(recordGapCenter + 353768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353768]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06474_not_prime : ¬(recordGapCenter + 353876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353876]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06475_not_prime : ¬(recordGapCenter + 353946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353946]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06476_not_prime : ¬(recordGapCenter + 353966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353966]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06477_not_prime : ¬(recordGapCenter + 353972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 353972]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06478_not_prime : ¬(recordGapCenter + 354092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354092]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06479_not_prime : ¬(recordGapCenter + 354126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354126]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06480_not_prime : ¬(recordGapCenter + 354182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354182]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06481_not_prime : ¬(recordGapCenter + 354422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354422]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06482_not_prime : ¬(recordGapCenter + 354446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354446]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06483_not_prime : ¬(recordGapCenter + 354572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354572]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06484_not_prime : ¬(recordGapCenter + 354758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354758]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06485_not_prime : ¬(recordGapCenter + 354816).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354816]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06486_not_prime : ¬(recordGapCenter + 354842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354842]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06487_not_prime : ¬(recordGapCenter + 354846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 354846]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06488_not_prime : ¬(recordGapCenter + 355002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355002]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06489_not_prime : ¬(recordGapCenter + 355022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355022]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06490_not_prime : ¬(recordGapCenter + 355182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355182]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06491_not_prime : ¬(recordGapCenter + 355478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355478]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06492_not_prime : ¬(recordGapCenter + 355526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355526]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06493_not_prime : ¬(recordGapCenter + 355622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355622]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06494_not_prime : ¬(recordGapCenter + 355638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355638]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06495_not_prime : ¬(recordGapCenter + 355686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355686]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06496_not_prime : ¬(recordGapCenter + 355766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355766]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06497_not_prime : ¬(recordGapCenter + 355826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355826]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06498_not_prime : ¬(recordGapCenter + 355988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 355988]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06499_not_prime : ¬(recordGapCenter + 356036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356036]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06500_not_prime : ¬(recordGapCenter + 356042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356042]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06501_not_prime : ¬(recordGapCenter + 356186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356186]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06502_not_prime : ¬(recordGapCenter + 356228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356228]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06503_not_prime : ¬(recordGapCenter + 356276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356276]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06504_not_prime : ¬(recordGapCenter + 356322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356322]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06505_not_prime : ¬(recordGapCenter + 356358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356358]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06506_not_prime : ¬(recordGapCenter + 356492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356492]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06507_not_prime : ¬(recordGapCenter + 356498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356498]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06508_not_prime : ¬(recordGapCenter + 356666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356666]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06509_not_prime : ¬(recordGapCenter + 356786).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356786]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06510_not_prime : ¬(recordGapCenter + 356802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356802]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06511_not_prime : ¬(recordGapCenter + 356882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356882]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06512_not_prime : ¬(recordGapCenter + 356948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356948]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06513_not_prime : ¬(recordGapCenter + 356982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 356982]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06514_not_prime : ¬(recordGapCenter + 357002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357002]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06515_not_prime : ¬(recordGapCenter + 357026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357026]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06516_not_prime : ¬(recordGapCenter + 357092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357092]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06517_not_prime : ¬(recordGapCenter + 357218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357218]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06518_not_prime : ¬(recordGapCenter + 357242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357242]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06519_not_prime : ¬(recordGapCenter + 357402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357402]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06520_not_prime : ¬(recordGapCenter + 357548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357548]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06521_not_prime : ¬(recordGapCenter + 357596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357596]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06522_not_prime : ¬(recordGapCenter + 357662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357662]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06523_not_prime : ¬(recordGapCenter + 357668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357668]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06524_not_prime : ¬(recordGapCenter + 357726).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357726]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06525_not_prime : ¬(recordGapCenter + 357746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357746]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06526_not_prime : ¬(recordGapCenter + 357806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357806]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06527_not_prime : ¬(recordGapCenter + 357908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357908]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

theorem fullRecordGapTerm06528_not_prime : ¬(recordGapCenter + 357978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 357978]
  · apply fullRecordGapRow00102_fermat
    simp [fullRecordGapRow00102_values]

end PrimeFactorUnimodality
