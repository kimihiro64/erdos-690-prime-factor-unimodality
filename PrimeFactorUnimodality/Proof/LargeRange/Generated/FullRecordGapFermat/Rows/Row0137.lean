import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00137_values : List Nat :=
  [fullRecordGapCenterValue + 520826,
    fullRecordGapCenterValue + 520838,
    fullRecordGapCenterValue + 520892,
    fullRecordGapCenterValue + 520922,
    fullRecordGapCenterValue + 520952,
    fullRecordGapCenterValue + 521012,
    fullRecordGapCenterValue + 521102,
    fullRecordGapCenterValue + 521106,
    fullRecordGapCenterValue + 521166,
    fullRecordGapCenterValue + 521210,
    fullRecordGapCenterValue + 521258,
    fullRecordGapCenterValue + 521270,
    fullRecordGapCenterValue + 521336,
    fullRecordGapCenterValue + 521426,
    fullRecordGapCenterValue + 521516,
    fullRecordGapCenterValue + 521522,
    fullRecordGapCenterValue + 521538,
    fullRecordGapCenterValue + 521582,
    fullRecordGapCenterValue + 521630,
    fullRecordGapCenterValue + 521810,
    fullRecordGapCenterValue + 521876,
    fullRecordGapCenterValue + 521882,
    fullRecordGapCenterValue + 521958,
    fullRecordGapCenterValue + 521988,
    fullRecordGapCenterValue + 522026,
    fullRecordGapCenterValue + 522068,
    fullRecordGapCenterValue + 522092,
    fullRecordGapCenterValue + 522152,
    fullRecordGapCenterValue + 522212,
    fullRecordGapCenterValue + 522230,
    fullRecordGapCenterValue + 522296,
    fullRecordGapCenterValue + 522476,
    fullRecordGapCenterValue + 522498,
    fullRecordGapCenterValue + 522572,
    fullRecordGapCenterValue + 522590,
    fullRecordGapCenterValue + 522596,
    fullRecordGapCenterValue + 522720,
    fullRecordGapCenterValue + 522758,
    fullRecordGapCenterValue + 522876,
    fullRecordGapCenterValue + 522902,
    fullRecordGapCenterValue + 522926,
    fullRecordGapCenterValue + 523058,
    fullRecordGapCenterValue + 523076,
    fullRecordGapCenterValue + 523148,
    fullRecordGapCenterValue + 523262,
    fullRecordGapCenterValue + 523268,
    fullRecordGapCenterValue + 523316,
    fullRecordGapCenterValue + 523436,
    fullRecordGapCenterValue + 523646,
    fullRecordGapCenterValue + 523758,
    fullRecordGapCenterValue + 523790,
    fullRecordGapCenterValue + 523812,
    fullRecordGapCenterValue + 523832,
    fullRecordGapCenterValue + 523938,
    fullRecordGapCenterValue + 523946,
    fullRecordGapCenterValue + 524252,
    fullRecordGapCenterValue + 524408,
    fullRecordGapCenterValue + 524562,
    fullRecordGapCenterValue + 524598,
    fullRecordGapCenterValue + 524658,
    fullRecordGapCenterValue + 524738,
    fullRecordGapCenterValue + 524918,
    fullRecordGapCenterValue + 524996,
    fullRecordGapCenterValue + 525036]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00137_fermat : ∀ n ∈ fullRecordGapRow00137_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08705_not_prime : ¬(recordGapCenter + 520826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520826]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08706_not_prime : ¬(recordGapCenter + 520838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520838]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08707_not_prime : ¬(recordGapCenter + 520892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520892]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08708_not_prime : ¬(recordGapCenter + 520922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520922]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08709_not_prime : ¬(recordGapCenter + 520952).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 520952]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08710_not_prime : ¬(recordGapCenter + 521012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521012]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08711_not_prime : ¬(recordGapCenter + 521102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521102]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08712_not_prime : ¬(recordGapCenter + 521106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521106]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08713_not_prime : ¬(recordGapCenter + 521166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521166]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08714_not_prime : ¬(recordGapCenter + 521210).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521210]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08715_not_prime : ¬(recordGapCenter + 521258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521258]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08716_not_prime : ¬(recordGapCenter + 521270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521270]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08717_not_prime : ¬(recordGapCenter + 521336).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521336]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08718_not_prime : ¬(recordGapCenter + 521426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521426]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08719_not_prime : ¬(recordGapCenter + 521516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521516]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08720_not_prime : ¬(recordGapCenter + 521522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521522]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08721_not_prime : ¬(recordGapCenter + 521538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521538]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08722_not_prime : ¬(recordGapCenter + 521582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521582]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08723_not_prime : ¬(recordGapCenter + 521630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521630]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08724_not_prime : ¬(recordGapCenter + 521810).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521810]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08725_not_prime : ¬(recordGapCenter + 521876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521876]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08726_not_prime : ¬(recordGapCenter + 521882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521882]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08727_not_prime : ¬(recordGapCenter + 521958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521958]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08728_not_prime : ¬(recordGapCenter + 521988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 521988]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08729_not_prime : ¬(recordGapCenter + 522026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522026]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08730_not_prime : ¬(recordGapCenter + 522068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522068]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08731_not_prime : ¬(recordGapCenter + 522092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522092]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08732_not_prime : ¬(recordGapCenter + 522152).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522152]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08733_not_prime : ¬(recordGapCenter + 522212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522212]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08734_not_prime : ¬(recordGapCenter + 522230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522230]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08735_not_prime : ¬(recordGapCenter + 522296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522296]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08736_not_prime : ¬(recordGapCenter + 522476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522476]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08737_not_prime : ¬(recordGapCenter + 522498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522498]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08738_not_prime : ¬(recordGapCenter + 522572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522572]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08739_not_prime : ¬(recordGapCenter + 522590).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522590]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08740_not_prime : ¬(recordGapCenter + 522596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522596]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08741_not_prime : ¬(recordGapCenter + 522720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522720]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08742_not_prime : ¬(recordGapCenter + 522758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522758]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08743_not_prime : ¬(recordGapCenter + 522876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522876]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08744_not_prime : ¬(recordGapCenter + 522902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522902]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08745_not_prime : ¬(recordGapCenter + 522926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 522926]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08746_not_prime : ¬(recordGapCenter + 523058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 523058]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08747_not_prime : ¬(recordGapCenter + 523076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 523076]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08748_not_prime : ¬(recordGapCenter + 523148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 523148]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08749_not_prime : ¬(recordGapCenter + 523262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 523262]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08750_not_prime : ¬(recordGapCenter + 523268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 523268]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08751_not_prime : ¬(recordGapCenter + 523316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 523316]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08752_not_prime : ¬(recordGapCenter + 523436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 523436]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08753_not_prime : ¬(recordGapCenter + 523646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 523646]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08754_not_prime : ¬(recordGapCenter + 523758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 523758]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08755_not_prime : ¬(recordGapCenter + 523790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 523790]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08756_not_prime : ¬(recordGapCenter + 523812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 523812]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08757_not_prime : ¬(recordGapCenter + 523832).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 523832]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08758_not_prime : ¬(recordGapCenter + 523938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 523938]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08759_not_prime : ¬(recordGapCenter + 523946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 523946]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08760_not_prime : ¬(recordGapCenter + 524252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 524252]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08761_not_prime : ¬(recordGapCenter + 524408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 524408]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08762_not_prime : ¬(recordGapCenter + 524562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 524562]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08763_not_prime : ¬(recordGapCenter + 524598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 524598]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08764_not_prime : ¬(recordGapCenter + 524658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 524658]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08765_not_prime : ¬(recordGapCenter + 524738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 524738]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08766_not_prime : ¬(recordGapCenter + 524918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 524918]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08767_not_prime : ¬(recordGapCenter + 524996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 524996]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

theorem fullRecordGapTerm08768_not_prime : ¬(recordGapCenter + 525036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 525036]
  · apply fullRecordGapRow00137_fermat
    simp [fullRecordGapRow00137_values]

end PrimeFactorUnimodality
