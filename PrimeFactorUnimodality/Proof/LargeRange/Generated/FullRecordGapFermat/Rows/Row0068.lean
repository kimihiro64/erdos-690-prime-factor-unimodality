import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00068_values : List Nat :=
  [fullRecordGapCenterValue + 123722,
    fullRecordGapCenterValue + 123750,
    fullRecordGapCenterValue + 123866,
    fullRecordGapCenterValue + 124022,
    fullRecordGapCenterValue + 124416,
    fullRecordGapCenterValue + 124740,
    fullRecordGapCenterValue + 124766,
    fullRecordGapCenterValue + 125078,
    fullRecordGapCenterValue + 125402,
    fullRecordGapCenterValue + 125486,
    fullRecordGapCenterValue + 125546,
    fullRecordGapCenterValue + 125582,
    fullRecordGapCenterValue + 125738,
    fullRecordGapCenterValue + 125966,
    fullRecordGapCenterValue + 126158,
    fullRecordGapCenterValue + 126662,
    fullRecordGapCenterValue + 126722,
    fullRecordGapCenterValue + 126842,
    fullRecordGapCenterValue + 126878,
    fullRecordGapCenterValue + 127008,
    fullRecordGapCenterValue + 127082,
    fullRecordGapCenterValue + 127118,
    fullRecordGapCenterValue + 127202,
    fullRecordGapCenterValue + 127776,
    fullRecordGapCenterValue + 127898,
    fullRecordGapCenterValue + 128306,
    fullRecordGapCenterValue + 128462,
    fullRecordGapCenterValue + 128606,
    fullRecordGapCenterValue + 128798,
    fullRecordGapCenterValue + 129266,
    fullRecordGapCenterValue + 129326,
    fullRecordGapCenterValue + 129360,
    fullRecordGapCenterValue + 129386,
    fullRecordGapCenterValue + 129566,
    fullRecordGapCenterValue + 129782,
    fullRecordGapCenterValue + 130022,
    fullRecordGapCenterValue + 130106,
    fullRecordGapCenterValue + 130142,
    fullRecordGapCenterValue + 130238,
    fullRecordGapCenterValue + 130406,
    fullRecordGapCenterValue + 130538,
    fullRecordGapCenterValue + 130646,
    fullRecordGapCenterValue + 130706,
    fullRecordGapCenterValue + 130826,
    fullRecordGapCenterValue + 131198,
    fullRecordGapCenterValue + 131220,
    fullRecordGapCenterValue + 131678,
    fullRecordGapCenterValue + 131702,
    fullRecordGapCenterValue + 131966,
    fullRecordGapCenterValue + 132338,
    fullRecordGapCenterValue + 132602,
    fullRecordGapCenterValue + 132686,
    fullRecordGapCenterValue + 132746,
    fullRecordGapCenterValue + 132926,
    fullRecordGapCenterValue + 132998,
    fullRecordGapCenterValue + 133056,
    fullRecordGapCenterValue + 133058,
    fullRecordGapCenterValue + 133106,
    fullRecordGapCenterValue + 133466,
    fullRecordGapCenterValue + 133478,
    fullRecordGapCenterValue + 133526,
    fullRecordGapCenterValue + 133682,
    fullRecordGapCenterValue + 134258,
    fullRecordGapCenterValue + 134750]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00068_fermat : ∀ n ∈ fullRecordGapRow00068_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04289_not_prime : ¬(recordGapCenter + 123722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123722]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04290_not_prime : ¬(recordGapCenter + 123750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123750]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04291_not_prime : ¬(recordGapCenter + 123866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 123866]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04292_not_prime : ¬(recordGapCenter + 124022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 124022]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04293_not_prime : ¬(recordGapCenter + 124416).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 124416]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04294_not_prime : ¬(recordGapCenter + 124740).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 124740]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04295_not_prime : ¬(recordGapCenter + 124766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 124766]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04296_not_prime : ¬(recordGapCenter + 125078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 125078]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04297_not_prime : ¬(recordGapCenter + 125402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 125402]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04298_not_prime : ¬(recordGapCenter + 125486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 125486]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04299_not_prime : ¬(recordGapCenter + 125546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 125546]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04300_not_prime : ¬(recordGapCenter + 125582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 125582]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04301_not_prime : ¬(recordGapCenter + 125738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 125738]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04302_not_prime : ¬(recordGapCenter + 125966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 125966]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04303_not_prime : ¬(recordGapCenter + 126158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 126158]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04304_not_prime : ¬(recordGapCenter + 126662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 126662]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04305_not_prime : ¬(recordGapCenter + 126722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 126722]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04306_not_prime : ¬(recordGapCenter + 126842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 126842]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04307_not_prime : ¬(recordGapCenter + 126878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 126878]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04308_not_prime : ¬(recordGapCenter + 127008).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 127008]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04309_not_prime : ¬(recordGapCenter + 127082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 127082]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04310_not_prime : ¬(recordGapCenter + 127118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 127118]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04311_not_prime : ¬(recordGapCenter + 127202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 127202]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04312_not_prime : ¬(recordGapCenter + 127776).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 127776]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04313_not_prime : ¬(recordGapCenter + 127898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 127898]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04314_not_prime : ¬(recordGapCenter + 128306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 128306]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04315_not_prime : ¬(recordGapCenter + 128462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 128462]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04316_not_prime : ¬(recordGapCenter + 128606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 128606]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04317_not_prime : ¬(recordGapCenter + 128798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 128798]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04318_not_prime : ¬(recordGapCenter + 129266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 129266]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04319_not_prime : ¬(recordGapCenter + 129326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 129326]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04320_not_prime : ¬(recordGapCenter + 129360).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 129360]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04321_not_prime : ¬(recordGapCenter + 129386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 129386]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04322_not_prime : ¬(recordGapCenter + 129566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 129566]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04323_not_prime : ¬(recordGapCenter + 129782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 129782]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04324_not_prime : ¬(recordGapCenter + 130022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130022]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04325_not_prime : ¬(recordGapCenter + 130106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130106]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04326_not_prime : ¬(recordGapCenter + 130142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130142]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04327_not_prime : ¬(recordGapCenter + 130238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130238]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04328_not_prime : ¬(recordGapCenter + 130406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130406]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04329_not_prime : ¬(recordGapCenter + 130538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130538]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04330_not_prime : ¬(recordGapCenter + 130646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130646]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04331_not_prime : ¬(recordGapCenter + 130706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130706]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04332_not_prime : ¬(recordGapCenter + 130826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 130826]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04333_not_prime : ¬(recordGapCenter + 131198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 131198]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04334_not_prime : ¬(recordGapCenter + 131220).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 131220]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04335_not_prime : ¬(recordGapCenter + 131678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 131678]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04336_not_prime : ¬(recordGapCenter + 131702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 131702]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04337_not_prime : ¬(recordGapCenter + 131966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 131966]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04338_not_prime : ¬(recordGapCenter + 132338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 132338]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04339_not_prime : ¬(recordGapCenter + 132602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 132602]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04340_not_prime : ¬(recordGapCenter + 132686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 132686]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04341_not_prime : ¬(recordGapCenter + 132746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 132746]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04342_not_prime : ¬(recordGapCenter + 132926).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 132926]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04343_not_prime : ¬(recordGapCenter + 132998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 132998]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04344_not_prime : ¬(recordGapCenter + 133056).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 133056]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04345_not_prime : ¬(recordGapCenter + 133058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 133058]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04346_not_prime : ¬(recordGapCenter + 133106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 133106]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04347_not_prime : ¬(recordGapCenter + 133466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 133466]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04348_not_prime : ¬(recordGapCenter + 133478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 133478]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04349_not_prime : ¬(recordGapCenter + 133526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 133526]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04350_not_prime : ¬(recordGapCenter + 133682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 133682]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04351_not_prime : ¬(recordGapCenter + 134258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 134258]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

theorem fullRecordGapTerm04352_not_prime : ¬(recordGapCenter + 134750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 134750]
  · apply fullRecordGapRow00068_fermat
    simp [fullRecordGapRow00068_values]

end PrimeFactorUnimodality
