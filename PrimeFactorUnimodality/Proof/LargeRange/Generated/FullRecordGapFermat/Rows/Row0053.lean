import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00053_values : List Nat :=
  [fullRecordGapCenterValue - 128218,
    fullRecordGapCenterValue - 128182,
    fullRecordGapCenterValue - 128134,
    fullRecordGapCenterValue - 128074,
    fullRecordGapCenterValue - 127858,
    fullRecordGapCenterValue - 127342,
    fullRecordGapCenterValue - 127294,
    fullRecordGapCenterValue - 127258,
    fullRecordGapCenterValue - 127234,
    fullRecordGapCenterValue - 127174,
    fullRecordGapCenterValue - 127042,
    fullRecordGapCenterValue - 127008,
    fullRecordGapCenterValue - 126838,
    fullRecordGapCenterValue - 126720,
    fullRecordGapCenterValue - 126622,
    fullRecordGapCenterValue - 126598,
    fullRecordGapCenterValue - 126562,
    fullRecordGapCenterValue - 126298,
    fullRecordGapCenterValue - 126118,
    fullRecordGapCenterValue - 125962,
    fullRecordGapCenterValue - 125842,
    fullRecordGapCenterValue - 125722,
    fullRecordGapCenterValue - 125638,
    fullRecordGapCenterValue - 124954,
    fullRecordGapCenterValue - 124702,
    fullRecordGapCenterValue - 124162,
    fullRecordGapCenterValue - 124114,
    fullRecordGapCenterValue - 123982,
    fullRecordGapCenterValue - 123958,
    fullRecordGapCenterValue - 123898,
    fullRecordGapCenterValue - 123562,
    fullRecordGapCenterValue - 123118,
    fullRecordGapCenterValue - 122880,
    fullRecordGapCenterValue - 122818,
    fullRecordGapCenterValue - 121834,
    fullRecordGapCenterValue - 121474,
    fullRecordGapCenterValue - 121438,
    fullRecordGapCenterValue - 121078,
    fullRecordGapCenterValue - 121042,
    fullRecordGapCenterValue - 120994,
    fullRecordGapCenterValue - 120514,
    fullRecordGapCenterValue - 120502,
    fullRecordGapCenterValue - 120214,
    fullRecordGapCenterValue - 120202,
    fullRecordGapCenterValue - 120154,
    fullRecordGapCenterValue - 120034,
    fullRecordGapCenterValue - 119914,
    fullRecordGapCenterValue - 119842,
    fullRecordGapCenterValue - 119758,
    fullRecordGapCenterValue - 119542,
    fullRecordGapCenterValue - 119338,
    fullRecordGapCenterValue - 119254,
    fullRecordGapCenterValue - 118942,
    fullRecordGapCenterValue - 118834,
    fullRecordGapCenterValue - 118800,
    fullRecordGapCenterValue - 118438,
    fullRecordGapCenterValue - 118414,
    fullRecordGapCenterValue - 118272,
    fullRecordGapCenterValue - 118138,
    fullRecordGapCenterValue - 118018,
    fullRecordGapCenterValue - 117934,
    fullRecordGapCenterValue - 117802,
    fullRecordGapCenterValue - 117778,
    fullRecordGapCenterValue - 117514]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00053_fermat : ∀ n ∈ fullRecordGapRow00053_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03329_not_prime : ¬(recordGapCenter - 128218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 128218]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03330_not_prime : ¬(recordGapCenter - 128182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 128182]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03331_not_prime : ¬(recordGapCenter - 128134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 128134]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03332_not_prime : ¬(recordGapCenter - 128074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 128074]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03333_not_prime : ¬(recordGapCenter - 127858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127858]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03334_not_prime : ¬(recordGapCenter - 127342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127342]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03335_not_prime : ¬(recordGapCenter - 127294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127294]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03336_not_prime : ¬(recordGapCenter - 127258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127258]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03337_not_prime : ¬(recordGapCenter - 127234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127234]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03338_not_prime : ¬(recordGapCenter - 127174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127174]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03339_not_prime : ¬(recordGapCenter - 127042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127042]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03340_not_prime : ¬(recordGapCenter - 127008).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127008]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03341_not_prime : ¬(recordGapCenter - 126838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 126838]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03342_not_prime : ¬(recordGapCenter - 126720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 126720]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03343_not_prime : ¬(recordGapCenter - 126622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 126622]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03344_not_prime : ¬(recordGapCenter - 126598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 126598]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03345_not_prime : ¬(recordGapCenter - 126562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 126562]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03346_not_prime : ¬(recordGapCenter - 126298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 126298]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03347_not_prime : ¬(recordGapCenter - 126118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 126118]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03348_not_prime : ¬(recordGapCenter - 125962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 125962]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03349_not_prime : ¬(recordGapCenter - 125842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 125842]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03350_not_prime : ¬(recordGapCenter - 125722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 125722]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03351_not_prime : ¬(recordGapCenter - 125638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 125638]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03352_not_prime : ¬(recordGapCenter - 124954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 124954]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03353_not_prime : ¬(recordGapCenter - 124702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 124702]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03354_not_prime : ¬(recordGapCenter - 124162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 124162]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03355_not_prime : ¬(recordGapCenter - 124114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 124114]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03356_not_prime : ¬(recordGapCenter - 123982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 123982]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03357_not_prime : ¬(recordGapCenter - 123958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 123958]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03358_not_prime : ¬(recordGapCenter - 123898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 123898]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03359_not_prime : ¬(recordGapCenter - 123562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 123562]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03360_not_prime : ¬(recordGapCenter - 123118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 123118]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03361_not_prime : ¬(recordGapCenter - 122880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 122880]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03362_not_prime : ¬(recordGapCenter - 122818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 122818]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03363_not_prime : ¬(recordGapCenter - 121834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 121834]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03364_not_prime : ¬(recordGapCenter - 121474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 121474]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03365_not_prime : ¬(recordGapCenter - 121438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 121438]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03366_not_prime : ¬(recordGapCenter - 121078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 121078]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03367_not_prime : ¬(recordGapCenter - 121042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 121042]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03368_not_prime : ¬(recordGapCenter - 120994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 120994]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03369_not_prime : ¬(recordGapCenter - 120514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 120514]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03370_not_prime : ¬(recordGapCenter - 120502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 120502]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03371_not_prime : ¬(recordGapCenter - 120214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 120214]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03372_not_prime : ¬(recordGapCenter - 120202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 120202]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03373_not_prime : ¬(recordGapCenter - 120154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 120154]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03374_not_prime : ¬(recordGapCenter - 120034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 120034]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03375_not_prime : ¬(recordGapCenter - 119914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 119914]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03376_not_prime : ¬(recordGapCenter - 119842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 119842]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03377_not_prime : ¬(recordGapCenter - 119758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 119758]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03378_not_prime : ¬(recordGapCenter - 119542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 119542]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03379_not_prime : ¬(recordGapCenter - 119338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 119338]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03380_not_prime : ¬(recordGapCenter - 119254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 119254]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03381_not_prime : ¬(recordGapCenter - 118942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118942]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03382_not_prime : ¬(recordGapCenter - 118834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118834]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03383_not_prime : ¬(recordGapCenter - 118800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118800]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03384_not_prime : ¬(recordGapCenter - 118438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118438]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03385_not_prime : ¬(recordGapCenter - 118414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118414]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03386_not_prime : ¬(recordGapCenter - 118272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118272]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03387_not_prime : ¬(recordGapCenter - 118138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118138]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03388_not_prime : ¬(recordGapCenter - 118018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118018]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03389_not_prime : ¬(recordGapCenter - 117934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 117934]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03390_not_prime : ¬(recordGapCenter - 117802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 117802]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03391_not_prime : ¬(recordGapCenter - 117778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 117778]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

theorem fullRecordGapTerm03392_not_prime : ¬(recordGapCenter - 117514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 117514]
  · apply fullRecordGapRow00053_fermat
    simp [fullRecordGapRow00053_values]

end PrimeFactorUnimodality
