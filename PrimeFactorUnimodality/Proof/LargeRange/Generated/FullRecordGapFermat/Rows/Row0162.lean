import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00162_values : List Nat :=
  [fullRecordGapCenterValue + 620928,
    fullRecordGapCenterValue + 620988,
    fullRecordGapCenterValue + 621128,
    fullRecordGapCenterValue + 621176,
    fullRecordGapCenterValue + 621182,
    fullRecordGapCenterValue + 621272,
    fullRecordGapCenterValue + 621290,
    fullRecordGapCenterValue + 621332,
    fullRecordGapCenterValue + 621366,
    fullRecordGapCenterValue + 621482,
    fullRecordGapCenterValue + 621542,
    fullRecordGapCenterValue + 621596,
    fullRecordGapCenterValue + 621602,
    fullRecordGapCenterValue + 621710,
    fullRecordGapCenterValue + 621722,
    fullRecordGapCenterValue + 621812,
    fullRecordGapCenterValue + 621938,
    fullRecordGapCenterValue + 621948,
    fullRecordGapCenterValue + 622010,
    fullRecordGapCenterValue + 622080,
    fullRecordGapCenterValue + 622308,
    fullRecordGapCenterValue + 622316,
    fullRecordGapCenterValue + 622406,
    fullRecordGapCenterValue + 622598,
    fullRecordGapCenterValue + 622652,
    fullRecordGapCenterValue + 622682,
    fullRecordGapCenterValue + 622730,
    fullRecordGapCenterValue + 622742,
    fullRecordGapCenterValue + 622806,
    fullRecordGapCenterValue + 622878,
    fullRecordGapCenterValue + 622956,
    fullRecordGapCenterValue + 622958,
    fullRecordGapCenterValue + 623148,
    fullRecordGapCenterValue + 623270,
    fullRecordGapCenterValue + 623306,
    fullRecordGapCenterValue + 623478,
    fullRecordGapCenterValue + 623486,
    fullRecordGapCenterValue + 623606,
    fullRecordGapCenterValue + 623676,
    fullRecordGapCenterValue + 623700,
    fullRecordGapCenterValue + 623738,
    fullRecordGapCenterValue + 623882,
    fullRecordGapCenterValue + 623886,
    fullRecordGapCenterValue + 623892,
    fullRecordGapCenterValue + 623946,
    fullRecordGapCenterValue + 624018,
    fullRecordGapCenterValue + 624062,
    fullRecordGapCenterValue + 624248,
    fullRecordGapCenterValue + 624282,
    fullRecordGapCenterValue + 624318,
    fullRecordGapCenterValue + 624458,
    fullRecordGapCenterValue + 624482,
    fullRecordGapCenterValue + 624506,
    fullRecordGapCenterValue + 624522,
    fullRecordGapCenterValue + 624578,
    fullRecordGapCenterValue + 624662,
    fullRecordGapCenterValue + 624678,
    fullRecordGapCenterValue + 624698,
    fullRecordGapCenterValue + 624738,
    fullRecordGapCenterValue + 624968,
    fullRecordGapCenterValue + 625028,
    fullRecordGapCenterValue + 625112,
    fullRecordGapCenterValue + 625202,
    fullRecordGapCenterValue + 625256]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00162_fermat : ∀ n ∈ fullRecordGapRow00162_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm10305_not_prime : ¬(recordGapCenter + 620928).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620928]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10306_not_prime : ¬(recordGapCenter + 620988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 620988]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10307_not_prime : ¬(recordGapCenter + 621128).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621128]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10308_not_prime : ¬(recordGapCenter + 621176).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621176]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10309_not_prime : ¬(recordGapCenter + 621182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621182]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10310_not_prime : ¬(recordGapCenter + 621272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621272]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10311_not_prime : ¬(recordGapCenter + 621290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621290]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10312_not_prime : ¬(recordGapCenter + 621332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621332]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10313_not_prime : ¬(recordGapCenter + 621366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621366]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10314_not_prime : ¬(recordGapCenter + 621482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621482]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10315_not_prime : ¬(recordGapCenter + 621542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621542]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10316_not_prime : ¬(recordGapCenter + 621596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621596]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10317_not_prime : ¬(recordGapCenter + 621602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621602]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10318_not_prime : ¬(recordGapCenter + 621710).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621710]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10319_not_prime : ¬(recordGapCenter + 621722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621722]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10320_not_prime : ¬(recordGapCenter + 621812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621812]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10321_not_prime : ¬(recordGapCenter + 621938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621938]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10322_not_prime : ¬(recordGapCenter + 621948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 621948]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10323_not_prime : ¬(recordGapCenter + 622010).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 622010]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10324_not_prime : ¬(recordGapCenter + 622080).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 622080]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10325_not_prime : ¬(recordGapCenter + 622308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 622308]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10326_not_prime : ¬(recordGapCenter + 622316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 622316]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10327_not_prime : ¬(recordGapCenter + 622406).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 622406]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10328_not_prime : ¬(recordGapCenter + 622598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 622598]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10329_not_prime : ¬(recordGapCenter + 622652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 622652]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10330_not_prime : ¬(recordGapCenter + 622682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 622682]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10331_not_prime : ¬(recordGapCenter + 622730).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 622730]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10332_not_prime : ¬(recordGapCenter + 622742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 622742]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10333_not_prime : ¬(recordGapCenter + 622806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 622806]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10334_not_prime : ¬(recordGapCenter + 622878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 622878]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10335_not_prime : ¬(recordGapCenter + 622956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 622956]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10336_not_prime : ¬(recordGapCenter + 622958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 622958]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10337_not_prime : ¬(recordGapCenter + 623148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 623148]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10338_not_prime : ¬(recordGapCenter + 623270).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 623270]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10339_not_prime : ¬(recordGapCenter + 623306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 623306]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10340_not_prime : ¬(recordGapCenter + 623478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 623478]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10341_not_prime : ¬(recordGapCenter + 623486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 623486]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10342_not_prime : ¬(recordGapCenter + 623606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 623606]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10343_not_prime : ¬(recordGapCenter + 623676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 623676]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10344_not_prime : ¬(recordGapCenter + 623700).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 623700]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10345_not_prime : ¬(recordGapCenter + 623738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 623738]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10346_not_prime : ¬(recordGapCenter + 623882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 623882]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10347_not_prime : ¬(recordGapCenter + 623886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 623886]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10348_not_prime : ¬(recordGapCenter + 623892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 623892]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10349_not_prime : ¬(recordGapCenter + 623946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 623946]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10350_not_prime : ¬(recordGapCenter + 624018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624018]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10351_not_prime : ¬(recordGapCenter + 624062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624062]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10352_not_prime : ¬(recordGapCenter + 624248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624248]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10353_not_prime : ¬(recordGapCenter + 624282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624282]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10354_not_prime : ¬(recordGapCenter + 624318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624318]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10355_not_prime : ¬(recordGapCenter + 624458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624458]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10356_not_prime : ¬(recordGapCenter + 624482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624482]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10357_not_prime : ¬(recordGapCenter + 624506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624506]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10358_not_prime : ¬(recordGapCenter + 624522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624522]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10359_not_prime : ¬(recordGapCenter + 624578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624578]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10360_not_prime : ¬(recordGapCenter + 624662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624662]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10361_not_prime : ¬(recordGapCenter + 624678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624678]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10362_not_prime : ¬(recordGapCenter + 624698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624698]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10363_not_prime : ¬(recordGapCenter + 624738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624738]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10364_not_prime : ¬(recordGapCenter + 624968).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 624968]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10365_not_prime : ¬(recordGapCenter + 625028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625028]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10366_not_prime : ¬(recordGapCenter + 625112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625112]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10367_not_prime : ¬(recordGapCenter + 625202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625202]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

theorem fullRecordGapTerm10368_not_prime : ¬(recordGapCenter + 625256).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 625256]
  · apply fullRecordGapRow00162_fermat
    simp [fullRecordGapRow00162_values]

end PrimeFactorUnimodality
