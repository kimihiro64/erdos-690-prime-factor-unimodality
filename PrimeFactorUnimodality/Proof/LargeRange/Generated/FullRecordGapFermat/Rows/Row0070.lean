import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00070_values : List Nat :=
  [fullRecordGapCenterValue + 144986,
    fullRecordGapCenterValue + 145118,
    fullRecordGapCenterValue + 145346,
    fullRecordGapCenterValue + 145358,
    fullRecordGapCenterValue + 145478,
    fullRecordGapCenterValue + 145530,
    fullRecordGapCenterValue + 145646,
    fullRecordGapCenterValue + 145800,
    fullRecordGapCenterValue + 145946,
    fullRecordGapCenterValue + 146282,
    fullRecordGapCenterValue + 146738,
    fullRecordGapCenterValue + 146906,
    fullRecordGapCenterValue + 146966,
    fullRecordGapCenterValue + 147386,
    fullRecordGapCenterValue + 147456,
    fullRecordGapCenterValue + 147698,
    fullRecordGapCenterValue + 147878,
    fullRecordGapCenterValue + 148142,
    fullRecordGapCenterValue + 148202,
    fullRecordGapCenterValue + 148262,
    fullRecordGapCenterValue + 148286,
    fullRecordGapCenterValue + 148766,
    fullRecordGapCenterValue + 149072,
    fullRecordGapCenterValue + 149306,
    fullRecordGapCenterValue + 149426,
    fullRecordGapCenterValue + 149438,
    fullRecordGapCenterValue + 149462,
    fullRecordGapCenterValue + 149642,
    fullRecordGapCenterValue + 149846,
    fullRecordGapCenterValue + 150000,
    fullRecordGapCenterValue + 150158,
    fullRecordGapCenterValue + 150266,
    fullRecordGapCenterValue + 150446,
    fullRecordGapCenterValue + 150578,
    fullRecordGapCenterValue + 150920,
    fullRecordGapCenterValue + 151142,
    fullRecordGapCenterValue + 151200,
    fullRecordGapCenterValue + 151250,
    fullRecordGapCenterValue + 151358,
    fullRecordGapCenterValue + 151586,
    fullRecordGapCenterValue + 151706,
    fullRecordGapCenterValue + 151826,
    fullRecordGapCenterValue + 152078,
    fullRecordGapCenterValue + 152162,
    fullRecordGapCenterValue + 152426,
    fullRecordGapCenterValue + 152462,
    fullRecordGapCenterValue + 152486,
    fullRecordGapCenterValue + 152738,
    fullRecordGapCenterValue + 153090,
    fullRecordGapCenterValue + 153158,
    fullRecordGapCenterValue + 153602,
    fullRecordGapCenterValue + 153638,
    fullRecordGapCenterValue + 153662,
    fullRecordGapCenterValue + 153746,
    fullRecordGapCenterValue + 154058,
    fullRecordGapCenterValue + 154082,
    fullRecordGapCenterValue + 155138,
    fullRecordGapCenterValue + 155232,
    fullRecordGapCenterValue + 155486,
    fullRecordGapCenterValue + 155520,
    fullRecordGapCenterValue + 155522,
    fullRecordGapCenterValue + 156062,
    fullRecordGapCenterValue + 156158,
    fullRecordGapCenterValue + 156242]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00070_fermat : ∀ n ∈ fullRecordGapRow00070_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04417_not_prime : ¬(recordGapCenter + 144986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 144986]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04418_not_prime : ¬(recordGapCenter + 145118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145118]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04419_not_prime : ¬(recordGapCenter + 145346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145346]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04420_not_prime : ¬(recordGapCenter + 145358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145358]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04421_not_prime : ¬(recordGapCenter + 145478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145478]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04422_not_prime : ¬(recordGapCenter + 145530).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145530]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04423_not_prime : ¬(recordGapCenter + 145646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145646]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04424_not_prime : ¬(recordGapCenter + 145800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145800]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04425_not_prime : ¬(recordGapCenter + 145946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 145946]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04426_not_prime : ¬(recordGapCenter + 146282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 146282]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04427_not_prime : ¬(recordGapCenter + 146738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 146738]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04428_not_prime : ¬(recordGapCenter + 146906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 146906]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04429_not_prime : ¬(recordGapCenter + 146966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 146966]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04430_not_prime : ¬(recordGapCenter + 147386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 147386]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04431_not_prime : ¬(recordGapCenter + 147456).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 147456]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04432_not_prime : ¬(recordGapCenter + 147698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 147698]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04433_not_prime : ¬(recordGapCenter + 147878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 147878]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04434_not_prime : ¬(recordGapCenter + 148142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 148142]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04435_not_prime : ¬(recordGapCenter + 148202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 148202]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04436_not_prime : ¬(recordGapCenter + 148262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 148262]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04437_not_prime : ¬(recordGapCenter + 148286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 148286]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04438_not_prime : ¬(recordGapCenter + 148766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 148766]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04439_not_prime : ¬(recordGapCenter + 149072).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 149072]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04440_not_prime : ¬(recordGapCenter + 149306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 149306]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04441_not_prime : ¬(recordGapCenter + 149426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 149426]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04442_not_prime : ¬(recordGapCenter + 149438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 149438]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04443_not_prime : ¬(recordGapCenter + 149462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 149462]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04444_not_prime : ¬(recordGapCenter + 149642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 149642]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04445_not_prime : ¬(recordGapCenter + 149846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 149846]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04446_not_prime : ¬(recordGapCenter + 150000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 150000]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04447_not_prime : ¬(recordGapCenter + 150158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 150158]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04448_not_prime : ¬(recordGapCenter + 150266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 150266]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04449_not_prime : ¬(recordGapCenter + 150446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 150446]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04450_not_prime : ¬(recordGapCenter + 150578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 150578]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04451_not_prime : ¬(recordGapCenter + 150920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 150920]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04452_not_prime : ¬(recordGapCenter + 151142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 151142]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04453_not_prime : ¬(recordGapCenter + 151200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 151200]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04454_not_prime : ¬(recordGapCenter + 151250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 151250]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04455_not_prime : ¬(recordGapCenter + 151358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 151358]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04456_not_prime : ¬(recordGapCenter + 151586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 151586]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04457_not_prime : ¬(recordGapCenter + 151706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 151706]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04458_not_prime : ¬(recordGapCenter + 151826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 151826]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04459_not_prime : ¬(recordGapCenter + 152078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 152078]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04460_not_prime : ¬(recordGapCenter + 152162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 152162]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04461_not_prime : ¬(recordGapCenter + 152426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 152426]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04462_not_prime : ¬(recordGapCenter + 152462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 152462]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04463_not_prime : ¬(recordGapCenter + 152486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 152486]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04464_not_prime : ¬(recordGapCenter + 152738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 152738]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04465_not_prime : ¬(recordGapCenter + 153090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 153090]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04466_not_prime : ¬(recordGapCenter + 153158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 153158]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04467_not_prime : ¬(recordGapCenter + 153602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 153602]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04468_not_prime : ¬(recordGapCenter + 153638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 153638]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04469_not_prime : ¬(recordGapCenter + 153662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 153662]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04470_not_prime : ¬(recordGapCenter + 153746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 153746]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04471_not_prime : ¬(recordGapCenter + 154058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 154058]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04472_not_prime : ¬(recordGapCenter + 154082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 154082]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04473_not_prime : ¬(recordGapCenter + 155138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 155138]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04474_not_prime : ¬(recordGapCenter + 155232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 155232]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04475_not_prime : ¬(recordGapCenter + 155486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 155486]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04476_not_prime : ¬(recordGapCenter + 155520).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 155520]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04477_not_prime : ¬(recordGapCenter + 155522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 155522]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04478_not_prime : ¬(recordGapCenter + 156062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 156062]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04479_not_prime : ¬(recordGapCenter + 156158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 156158]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

theorem fullRecordGapTerm04480_not_prime : ¬(recordGapCenter + 156242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 156242]
  · apply fullRecordGapRow00070_fermat
    simp [fullRecordGapRow00070_values]

end PrimeFactorUnimodality
