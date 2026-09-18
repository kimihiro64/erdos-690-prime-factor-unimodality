import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00039_values : List Nat :=
  [fullRecordGapCenterValue - 252262,
    fullRecordGapCenterValue - 252082,
    fullRecordGapCenterValue - 252000,
    fullRecordGapCenterValue - 251422,
    fullRecordGapCenterValue - 251374,
    fullRecordGapCenterValue - 251242,
    fullRecordGapCenterValue - 251194,
    fullRecordGapCenterValue - 251164,
    fullRecordGapCenterValue - 251092,
    fullRecordGapCenterValue - 251044,
    fullRecordGapCenterValue - 250924,
    fullRecordGapCenterValue - 250882,
    fullRecordGapCenterValue - 250858,
    fullRecordGapCenterValue - 250798,
    fullRecordGapCenterValue - 250522,
    fullRecordGapCenterValue - 250462,
    fullRecordGapCenterValue - 250414,
    fullRecordGapCenterValue - 250402,
    fullRecordGapCenterValue - 250000,
    fullRecordGapCenterValue - 249988,
    fullRecordGapCenterValue - 249982,
    fullRecordGapCenterValue - 249598,
    fullRecordGapCenterValue - 249538,
    fullRecordGapCenterValue - 249532,
    fullRecordGapCenterValue - 249478,
    fullRecordGapCenterValue - 249388,
    fullRecordGapCenterValue - 248932,
    fullRecordGapCenterValue - 248764,
    fullRecordGapCenterValue - 248734,
    fullRecordGapCenterValue - 248674,
    fullRecordGapCenterValue - 248602,
    fullRecordGapCenterValue - 248554,
    fullRecordGapCenterValue - 248278,
    fullRecordGapCenterValue - 248194,
    fullRecordGapCenterValue - 248134,
    fullRecordGapCenterValue - 248068,
    fullRecordGapCenterValue - 248044,
    fullRecordGapCenterValue - 247774,
    fullRecordGapCenterValue - 247732,
    fullRecordGapCenterValue - 247642,
    fullRecordGapCenterValue - 247582,
    fullRecordGapCenterValue - 247474,
    fullRecordGapCenterValue - 247348,
    fullRecordGapCenterValue - 246838,
    fullRecordGapCenterValue - 246802,
    fullRecordGapCenterValue - 246754,
    fullRecordGapCenterValue - 246628,
    fullRecordGapCenterValue - 246622,
    fullRecordGapCenterValue - 246538,
    fullRecordGapCenterValue - 246508,
    fullRecordGapCenterValue - 246418,
    fullRecordGapCenterValue - 246412,
    fullRecordGapCenterValue - 246400,
    fullRecordGapCenterValue - 246244,
    fullRecordGapCenterValue - 246172,
    fullRecordGapCenterValue - 246154,
    fullRecordGapCenterValue - 245914,
    fullRecordGapCenterValue - 245884,
    fullRecordGapCenterValue - 245878,
    fullRecordGapCenterValue - 245782,
    fullRecordGapCenterValue - 245760,
    fullRecordGapCenterValue - 245734,
    fullRecordGapCenterValue - 245668,
    fullRecordGapCenterValue - 245452]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00039_fermat : ∀ n ∈ fullRecordGapRow00039_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02433_not_prime : ¬(recordGapCenter - 252262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252262]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02434_not_prime : ¬(recordGapCenter - 252082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252082]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02435_not_prime : ¬(recordGapCenter - 252000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252000]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02436_not_prime : ¬(recordGapCenter - 251422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 251422]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02437_not_prime : ¬(recordGapCenter - 251374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 251374]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02438_not_prime : ¬(recordGapCenter - 251242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 251242]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02439_not_prime : ¬(recordGapCenter - 251194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 251194]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02440_not_prime : ¬(recordGapCenter - 251164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 251164]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02441_not_prime : ¬(recordGapCenter - 251092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 251092]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02442_not_prime : ¬(recordGapCenter - 251044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 251044]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02443_not_prime : ¬(recordGapCenter - 250924).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250924]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02444_not_prime : ¬(recordGapCenter - 250882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250882]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02445_not_prime : ¬(recordGapCenter - 250858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250858]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02446_not_prime : ¬(recordGapCenter - 250798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250798]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02447_not_prime : ¬(recordGapCenter - 250522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250522]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02448_not_prime : ¬(recordGapCenter - 250462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250462]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02449_not_prime : ¬(recordGapCenter - 250414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250414]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02450_not_prime : ¬(recordGapCenter - 250402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250402]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02451_not_prime : ¬(recordGapCenter - 250000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250000]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02452_not_prime : ¬(recordGapCenter - 249988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 249988]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02453_not_prime : ¬(recordGapCenter - 249982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 249982]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02454_not_prime : ¬(recordGapCenter - 249598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 249598]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02455_not_prime : ¬(recordGapCenter - 249538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 249538]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02456_not_prime : ¬(recordGapCenter - 249532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 249532]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02457_not_prime : ¬(recordGapCenter - 249478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 249478]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02458_not_prime : ¬(recordGapCenter - 249388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 249388]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02459_not_prime : ¬(recordGapCenter - 248932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248932]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02460_not_prime : ¬(recordGapCenter - 248764).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248764]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02461_not_prime : ¬(recordGapCenter - 248734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248734]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02462_not_prime : ¬(recordGapCenter - 248674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248674]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02463_not_prime : ¬(recordGapCenter - 248602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248602]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02464_not_prime : ¬(recordGapCenter - 248554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248554]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02465_not_prime : ¬(recordGapCenter - 248278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248278]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02466_not_prime : ¬(recordGapCenter - 248194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248194]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02467_not_prime : ¬(recordGapCenter - 248134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248134]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02468_not_prime : ¬(recordGapCenter - 248068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248068]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02469_not_prime : ¬(recordGapCenter - 248044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248044]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02470_not_prime : ¬(recordGapCenter - 247774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 247774]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02471_not_prime : ¬(recordGapCenter - 247732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 247732]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02472_not_prime : ¬(recordGapCenter - 247642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 247642]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02473_not_prime : ¬(recordGapCenter - 247582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 247582]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02474_not_prime : ¬(recordGapCenter - 247474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 247474]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02475_not_prime : ¬(recordGapCenter - 247348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 247348]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02476_not_prime : ¬(recordGapCenter - 246838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246838]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02477_not_prime : ¬(recordGapCenter - 246802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246802]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02478_not_prime : ¬(recordGapCenter - 246754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246754]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02479_not_prime : ¬(recordGapCenter - 246628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246628]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02480_not_prime : ¬(recordGapCenter - 246622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246622]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02481_not_prime : ¬(recordGapCenter - 246538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246538]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02482_not_prime : ¬(recordGapCenter - 246508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246508]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02483_not_prime : ¬(recordGapCenter - 246418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246418]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02484_not_prime : ¬(recordGapCenter - 246412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246412]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02485_not_prime : ¬(recordGapCenter - 246400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246400]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02486_not_prime : ¬(recordGapCenter - 246244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246244]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02487_not_prime : ¬(recordGapCenter - 246172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246172]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02488_not_prime : ¬(recordGapCenter - 246154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246154]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02489_not_prime : ¬(recordGapCenter - 245914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245914]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02490_not_prime : ¬(recordGapCenter - 245884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245884]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02491_not_prime : ¬(recordGapCenter - 245878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245878]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02492_not_prime : ¬(recordGapCenter - 245782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245782]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02493_not_prime : ¬(recordGapCenter - 245760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245760]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02494_not_prime : ¬(recordGapCenter - 245734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245734]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02495_not_prime : ¬(recordGapCenter - 245668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245668]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

theorem fullRecordGapTerm02496_not_prime : ¬(recordGapCenter - 245452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245452]
  · apply fullRecordGapRow00039_fermat
    simp [fullRecordGapRow00039_values]

end PrimeFactorUnimodality
