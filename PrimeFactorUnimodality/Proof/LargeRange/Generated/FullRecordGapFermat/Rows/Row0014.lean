import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00014_values : List Nat :=
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
    fullRecordGapCenterValue - 117514,
    fullRecordGapCenterValue - 117358,
    fullRecordGapCenterValue - 116962,
    fullRecordGapCenterValue - 116902,
    fullRecordGapCenterValue - 116878,
    fullRecordGapCenterValue - 116458,
    fullRecordGapCenterValue - 116424,
    fullRecordGapCenterValue - 116422,
    fullRecordGapCenterValue - 116134,
    fullRecordGapCenterValue - 115762,
    fullRecordGapCenterValue - 115500,
    fullRecordGapCenterValue - 115114,
    fullRecordGapCenterValue - 115054,
    fullRecordGapCenterValue - 114694,
    fullRecordGapCenterValue - 114658,
    fullRecordGapCenterValue - 114502,
    fullRecordGapCenterValue - 114442,
    fullRecordGapCenterValue - 114298,
    fullRecordGapCenterValue - 113914,
    fullRecordGapCenterValue - 113902,
    fullRecordGapCenterValue - 113794,
    fullRecordGapCenterValue - 113494,
    fullRecordGapCenterValue - 113362,
    fullRecordGapCenterValue - 113038,
    fullRecordGapCenterValue - 112954,
    fullRecordGapCenterValue - 112738,
    fullRecordGapCenterValue - 112500,
    fullRecordGapCenterValue - 112474,
    fullRecordGapCenterValue - 112198,
    fullRecordGapCenterValue - 112018,
    fullRecordGapCenterValue - 112000,
    fullRecordGapCenterValue - 111934,
    fullRecordGapCenterValue - 111804,
    fullRecordGapCenterValue - 111802,
    fullRecordGapCenterValue - 111634,
    fullRecordGapCenterValue - 111394,
    fullRecordGapCenterValue - 111382,
    fullRecordGapCenterValue - 111334,
    fullRecordGapCenterValue - 111132,
    fullRecordGapCenterValue - 111022,
    fullRecordGapCenterValue - 110914,
    fullRecordGapCenterValue - 110674,
    fullRecordGapCenterValue - 110592,
    fullRecordGapCenterValue - 110458,
    fullRecordGapCenterValue - 110434,
    fullRecordGapCenterValue - 110250,
    fullRecordGapCenterValue - 108898,
    fullRecordGapCenterValue - 108874,
    fullRecordGapCenterValue - 108694,
    fullRecordGapCenterValue - 108502,
    fullRecordGapCenterValue - 107974,
    fullRecordGapCenterValue - 107902,
    fullRecordGapCenterValue - 107854,
    fullRecordGapCenterValue - 107800,
    fullRecordGapCenterValue - 107698,
    fullRecordGapCenterValue - 107662,
    fullRecordGapCenterValue - 107314,
    fullRecordGapCenterValue - 107278,
    fullRecordGapCenterValue - 107218,
    fullRecordGapCenterValue - 107194,
    fullRecordGapCenterValue - 107014,
    fullRecordGapCenterValue - 106722,
    fullRecordGapCenterValue - 106654,
    fullRecordGapCenterValue - 106402,
    fullRecordGapCenterValue - 106342,
    fullRecordGapCenterValue - 106294,
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
    fullRecordGapCenterValue - 96000,
    fullRecordGapCenterValue - 95962,
    fullRecordGapCenterValue - 95878,
    fullRecordGapCenterValue - 95554,
    fullRecordGapCenterValue - 95482,
    fullRecordGapCenterValue - 95434,
    fullRecordGapCenterValue - 95422,
    fullRecordGapCenterValue - 95398,
    fullRecordGapCenterValue - 95218,
    fullRecordGapCenterValue - 94918,
    fullRecordGapCenterValue - 94864,
    fullRecordGapCenterValue - 94762,
    fullRecordGapCenterValue - 94702,
    fullRecordGapCenterValue - 94678,
    fullRecordGapCenterValue - 94500,
    fullRecordGapCenterValue - 94474,
    fullRecordGapCenterValue - 94258,
    fullRecordGapCenterValue - 93994,
    fullRecordGapCenterValue - 93838,
    fullRecordGapCenterValue - 93778,
    fullRecordGapCenterValue - 93634,
    fullRecordGapCenterValue - 93538,
    fullRecordGapCenterValue - 93358,
    fullRecordGapCenterValue - 93312,
    fullRecordGapCenterValue - 93202,
    fullRecordGapCenterValue - 93022,
    fullRecordGapCenterValue - 92914,
    fullRecordGapCenterValue - 92698,
    fullRecordGapCenterValue - 92614,
    fullRecordGapCenterValue - 92398,
    fullRecordGapCenterValue - 92374,
    fullRecordGapCenterValue - 92182,
    fullRecordGapCenterValue - 92160,
    fullRecordGapCenterValue - 92098,
    fullRecordGapCenterValue - 91774,
    fullRecordGapCenterValue - 91738,
    fullRecordGapCenterValue - 91654,
    fullRecordGapCenterValue - 91534,
    fullRecordGapCenterValue - 91138,
    fullRecordGapCenterValue - 91114,
    fullRecordGapCenterValue - 90778,
    fullRecordGapCenterValue - 90720,
    fullRecordGapCenterValue - 90634,
    fullRecordGapCenterValue - 90562,
    fullRecordGapCenterValue - 90382,
    fullRecordGapCenterValue - 90274,
    fullRecordGapCenterValue - 90262,
    fullRecordGapCenterValue - 89878,
    fullRecordGapCenterValue - 89758,
    fullRecordGapCenterValue - 89638,
    fullRecordGapCenterValue - 89578,
    fullRecordGapCenterValue - 89542,
    fullRecordGapCenterValue - 89422,
    fullRecordGapCenterValue - 89374,
    fullRecordGapCenterValue - 89100,
    fullRecordGapCenterValue - 89098,
    fullRecordGapCenterValue - 89014,
    fullRecordGapCenterValue - 88762,
    fullRecordGapCenterValue - 88704,
    fullRecordGapCenterValue - 88702,
    fullRecordGapCenterValue - 88498,
    fullRecordGapCenterValue - 88414,
    fullRecordGapCenterValue - 88402,
    fullRecordGapCenterValue - 88342,
    fullRecordGapCenterValue - 88042]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00014_fermat : ∀ n ∈ fullRecordGapRow00014_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm03329_not_prime : ¬(recordGapCenter - 128218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 128218]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03330_not_prime : ¬(recordGapCenter - 128182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 128182]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03331_not_prime : ¬(recordGapCenter - 128134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 128134]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03332_not_prime : ¬(recordGapCenter - 128074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 128074]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03333_not_prime : ¬(recordGapCenter - 127858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127858]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03334_not_prime : ¬(recordGapCenter - 127342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127342]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03335_not_prime : ¬(recordGapCenter - 127294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127294]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03336_not_prime : ¬(recordGapCenter - 127258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127258]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03337_not_prime : ¬(recordGapCenter - 127234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127234]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03338_not_prime : ¬(recordGapCenter - 127174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127174]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03339_not_prime : ¬(recordGapCenter - 127042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127042]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03340_not_prime : ¬(recordGapCenter - 127008).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 127008]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03341_not_prime : ¬(recordGapCenter - 126838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 126838]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03342_not_prime : ¬(recordGapCenter - 126720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 126720]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03343_not_prime : ¬(recordGapCenter - 126622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 126622]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03344_not_prime : ¬(recordGapCenter - 126598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 126598]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03345_not_prime : ¬(recordGapCenter - 126562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 126562]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03346_not_prime : ¬(recordGapCenter - 126298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 126298]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03347_not_prime : ¬(recordGapCenter - 126118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 126118]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03348_not_prime : ¬(recordGapCenter - 125962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 125962]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03349_not_prime : ¬(recordGapCenter - 125842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 125842]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03350_not_prime : ¬(recordGapCenter - 125722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 125722]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03351_not_prime : ¬(recordGapCenter - 125638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 125638]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03352_not_prime : ¬(recordGapCenter - 124954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 124954]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03353_not_prime : ¬(recordGapCenter - 124702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 124702]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03354_not_prime : ¬(recordGapCenter - 124162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 124162]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03355_not_prime : ¬(recordGapCenter - 124114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 124114]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03356_not_prime : ¬(recordGapCenter - 123982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 123982]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03357_not_prime : ¬(recordGapCenter - 123958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 123958]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03358_not_prime : ¬(recordGapCenter - 123898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 123898]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03359_not_prime : ¬(recordGapCenter - 123562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 123562]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03360_not_prime : ¬(recordGapCenter - 123118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 123118]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03361_not_prime : ¬(recordGapCenter - 122880).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 122880]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03362_not_prime : ¬(recordGapCenter - 122818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 122818]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03363_not_prime : ¬(recordGapCenter - 121834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 121834]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03364_not_prime : ¬(recordGapCenter - 121474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 121474]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03365_not_prime : ¬(recordGapCenter - 121438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 121438]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03366_not_prime : ¬(recordGapCenter - 121078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 121078]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03367_not_prime : ¬(recordGapCenter - 121042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 121042]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03368_not_prime : ¬(recordGapCenter - 120994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 120994]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03369_not_prime : ¬(recordGapCenter - 120514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 120514]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03370_not_prime : ¬(recordGapCenter - 120502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 120502]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03371_not_prime : ¬(recordGapCenter - 120214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 120214]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03372_not_prime : ¬(recordGapCenter - 120202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 120202]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03373_not_prime : ¬(recordGapCenter - 120154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 120154]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03374_not_prime : ¬(recordGapCenter - 120034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 120034]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03375_not_prime : ¬(recordGapCenter - 119914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 119914]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03376_not_prime : ¬(recordGapCenter - 119842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 119842]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03377_not_prime : ¬(recordGapCenter - 119758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 119758]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03378_not_prime : ¬(recordGapCenter - 119542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 119542]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03379_not_prime : ¬(recordGapCenter - 119338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 119338]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03380_not_prime : ¬(recordGapCenter - 119254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 119254]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03381_not_prime : ¬(recordGapCenter - 118942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118942]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03382_not_prime : ¬(recordGapCenter - 118834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118834]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03383_not_prime : ¬(recordGapCenter - 118800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118800]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03384_not_prime : ¬(recordGapCenter - 118438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118438]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03385_not_prime : ¬(recordGapCenter - 118414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118414]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03386_not_prime : ¬(recordGapCenter - 118272).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118272]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03387_not_prime : ¬(recordGapCenter - 118138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118138]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03388_not_prime : ¬(recordGapCenter - 118018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 118018]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03389_not_prime : ¬(recordGapCenter - 117934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 117934]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03390_not_prime : ¬(recordGapCenter - 117802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 117802]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03391_not_prime : ¬(recordGapCenter - 117778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 117778]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03392_not_prime : ¬(recordGapCenter - 117514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 117514]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03393_not_prime : ¬(recordGapCenter - 117358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 117358]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03394_not_prime : ¬(recordGapCenter - 116962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 116962]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03395_not_prime : ¬(recordGapCenter - 116902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 116902]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03396_not_prime : ¬(recordGapCenter - 116878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 116878]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03397_not_prime : ¬(recordGapCenter - 116458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 116458]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03398_not_prime : ¬(recordGapCenter - 116424).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 116424]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03399_not_prime : ¬(recordGapCenter - 116422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 116422]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03400_not_prime : ¬(recordGapCenter - 116134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 116134]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03401_not_prime : ¬(recordGapCenter - 115762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 115762]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03402_not_prime : ¬(recordGapCenter - 115500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 115500]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03403_not_prime : ¬(recordGapCenter - 115114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 115114]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03404_not_prime : ¬(recordGapCenter - 115054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 115054]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03405_not_prime : ¬(recordGapCenter - 114694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 114694]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03406_not_prime : ¬(recordGapCenter - 114658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 114658]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03407_not_prime : ¬(recordGapCenter - 114502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 114502]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03408_not_prime : ¬(recordGapCenter - 114442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 114442]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03409_not_prime : ¬(recordGapCenter - 114298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 114298]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03410_not_prime : ¬(recordGapCenter - 113914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 113914]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03411_not_prime : ¬(recordGapCenter - 113902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 113902]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03412_not_prime : ¬(recordGapCenter - 113794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 113794]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03413_not_prime : ¬(recordGapCenter - 113494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 113494]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03414_not_prime : ¬(recordGapCenter - 113362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 113362]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03415_not_prime : ¬(recordGapCenter - 113038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 113038]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03416_not_prime : ¬(recordGapCenter - 112954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 112954]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03417_not_prime : ¬(recordGapCenter - 112738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 112738]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03418_not_prime : ¬(recordGapCenter - 112500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 112500]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03419_not_prime : ¬(recordGapCenter - 112474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 112474]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03420_not_prime : ¬(recordGapCenter - 112198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 112198]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03421_not_prime : ¬(recordGapCenter - 112018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 112018]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03422_not_prime : ¬(recordGapCenter - 112000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 112000]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03423_not_prime : ¬(recordGapCenter - 111934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111934]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03424_not_prime : ¬(recordGapCenter - 111804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111804]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03425_not_prime : ¬(recordGapCenter - 111802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111802]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03426_not_prime : ¬(recordGapCenter - 111634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111634]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03427_not_prime : ¬(recordGapCenter - 111394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111394]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03428_not_prime : ¬(recordGapCenter - 111382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111382]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03429_not_prime : ¬(recordGapCenter - 111334).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111334]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03430_not_prime : ¬(recordGapCenter - 111132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111132]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03431_not_prime : ¬(recordGapCenter - 111022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 111022]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03432_not_prime : ¬(recordGapCenter - 110914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 110914]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03433_not_prime : ¬(recordGapCenter - 110674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 110674]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03434_not_prime : ¬(recordGapCenter - 110592).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 110592]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03435_not_prime : ¬(recordGapCenter - 110458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 110458]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03436_not_prime : ¬(recordGapCenter - 110434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 110434]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03437_not_prime : ¬(recordGapCenter - 110250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 110250]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03438_not_prime : ¬(recordGapCenter - 108898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 108898]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03439_not_prime : ¬(recordGapCenter - 108874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 108874]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03440_not_prime : ¬(recordGapCenter - 108694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 108694]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03441_not_prime : ¬(recordGapCenter - 108502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 108502]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03442_not_prime : ¬(recordGapCenter - 107974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107974]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03443_not_prime : ¬(recordGapCenter - 107902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107902]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03444_not_prime : ¬(recordGapCenter - 107854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107854]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03445_not_prime : ¬(recordGapCenter - 107800).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107800]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03446_not_prime : ¬(recordGapCenter - 107698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107698]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03447_not_prime : ¬(recordGapCenter - 107662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107662]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03448_not_prime : ¬(recordGapCenter - 107314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107314]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03449_not_prime : ¬(recordGapCenter - 107278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107278]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03450_not_prime : ¬(recordGapCenter - 107218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107218]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03451_not_prime : ¬(recordGapCenter - 107194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107194]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03452_not_prime : ¬(recordGapCenter - 107014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 107014]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03453_not_prime : ¬(recordGapCenter - 106722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106722]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03454_not_prime : ¬(recordGapCenter - 106654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106654]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03455_not_prime : ¬(recordGapCenter - 106402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106402]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03456_not_prime : ¬(recordGapCenter - 106342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106342]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03457_not_prime : ¬(recordGapCenter - 106294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106294]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03458_not_prime : ¬(recordGapCenter - 106258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106258]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03459_not_prime : ¬(recordGapCenter - 106234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106234]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03460_not_prime : ¬(recordGapCenter - 106174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106174]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03461_not_prime : ¬(recordGapCenter - 106102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 106102]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03462_not_prime : ¬(recordGapCenter - 105838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 105838]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03463_not_prime : ¬(recordGapCenter - 105454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 105454]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03464_not_prime : ¬(recordGapCenter - 105394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 105394]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03465_not_prime : ¬(recordGapCenter - 105082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 105082]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03466_not_prime : ¬(recordGapCenter - 105058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 105058]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03467_not_prime : ¬(recordGapCenter - 104722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 104722]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03468_not_prime : ¬(recordGapCenter - 104544).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 104544]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03469_not_prime : ¬(recordGapCenter - 104362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 104362]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03470_not_prime : ¬(recordGapCenter - 103858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 103858]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03471_not_prime : ¬(recordGapCenter - 103498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 103498]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03472_not_prime : ¬(recordGapCenter - 103488).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 103488]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03473_not_prime : ¬(recordGapCenter - 103438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 103438]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03474_not_prime : ¬(recordGapCenter - 103078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 103078]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03475_not_prime : ¬(recordGapCenter - 102958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102958]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03476_not_prime : ¬(recordGapCenter - 102874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102874]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03477_not_prime : ¬(recordGapCenter - 102694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102694]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03478_not_prime : ¬(recordGapCenter - 102658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102658]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03479_not_prime : ¬(recordGapCenter - 102514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102514]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03480_not_prime : ¬(recordGapCenter - 102478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102478]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03481_not_prime : ¬(recordGapCenter - 102262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102262]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03482_not_prime : ¬(recordGapCenter - 102142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102142]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03483_not_prime : ¬(recordGapCenter - 102118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102118]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03484_not_prime : ¬(recordGapCenter - 102094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102094]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03485_not_prime : ¬(recordGapCenter - 102060).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 102060]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03486_not_prime : ¬(recordGapCenter - 101302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 101302]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03487_not_prime : ¬(recordGapCenter - 101254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 101254]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03488_not_prime : ¬(recordGapCenter - 101250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 101250]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03489_not_prime : ¬(recordGapCenter - 101098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 101098]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03490_not_prime : ¬(recordGapCenter - 100834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 100834]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03491_not_prime : ¬(recordGapCenter - 100774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 100774]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03492_not_prime : ¬(recordGapCenter - 100222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 100222]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03493_not_prime : ¬(recordGapCenter - 100174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 100174]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03494_not_prime : ¬(recordGapCenter - 100000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 100000]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03495_not_prime : ¬(recordGapCenter - 99874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 99874]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03496_not_prime : ¬(recordGapCenter - 99754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 99754]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03497_not_prime : ¬(recordGapCenter - 99742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 99742]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03498_not_prime : ¬(recordGapCenter - 99622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 99622]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03499_not_prime : ¬(recordGapCenter - 99574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 99574]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03500_not_prime : ¬(recordGapCenter - 99454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 99454]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03501_not_prime : ¬(recordGapCenter - 99000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 99000]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03502_not_prime : ¬(recordGapCenter - 98962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98962]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03503_not_prime : ¬(recordGapCenter - 98818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98818]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03504_not_prime : ¬(recordGapCenter - 98662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98662]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03505_not_prime : ¬(recordGapCenter - 98614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98614]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03506_not_prime : ¬(recordGapCenter - 98422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98422]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03507_not_prime : ¬(recordGapCenter - 98314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98314]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03508_not_prime : ¬(recordGapCenter - 98304).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98304]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03509_not_prime : ¬(recordGapCenter - 98074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98074]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03510_not_prime : ¬(recordGapCenter - 98062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 98062]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03511_not_prime : ¬(recordGapCenter - 97738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 97738]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03512_not_prime : ¬(recordGapCenter - 97558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 97558]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03513_not_prime : ¬(recordGapCenter - 97054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 97054]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03514_not_prime : ¬(recordGapCenter - 97020).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 97020]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03515_not_prime : ¬(recordGapCenter - 96898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 96898]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03516_not_prime : ¬(recordGapCenter - 96682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 96682]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03517_not_prime : ¬(recordGapCenter - 96598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 96598]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03518_not_prime : ¬(recordGapCenter - 96394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 96394]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03519_not_prime : ¬(recordGapCenter - 96228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 96228]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03520_not_prime : ¬(recordGapCenter - 96000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 96000]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03521_not_prime : ¬(recordGapCenter - 95962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95962]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03522_not_prime : ¬(recordGapCenter - 95878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95878]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03523_not_prime : ¬(recordGapCenter - 95554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95554]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03524_not_prime : ¬(recordGapCenter - 95482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95482]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03525_not_prime : ¬(recordGapCenter - 95434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95434]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03526_not_prime : ¬(recordGapCenter - 95422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95422]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03527_not_prime : ¬(recordGapCenter - 95398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95398]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03528_not_prime : ¬(recordGapCenter - 95218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 95218]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03529_not_prime : ¬(recordGapCenter - 94918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94918]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03530_not_prime : ¬(recordGapCenter - 94864).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94864]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03531_not_prime : ¬(recordGapCenter - 94762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94762]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03532_not_prime : ¬(recordGapCenter - 94702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94702]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03533_not_prime : ¬(recordGapCenter - 94678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94678]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03534_not_prime : ¬(recordGapCenter - 94500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94500]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03535_not_prime : ¬(recordGapCenter - 94474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94474]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03536_not_prime : ¬(recordGapCenter - 94258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 94258]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03537_not_prime : ¬(recordGapCenter - 93994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93994]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03538_not_prime : ¬(recordGapCenter - 93838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93838]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03539_not_prime : ¬(recordGapCenter - 93778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93778]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03540_not_prime : ¬(recordGapCenter - 93634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93634]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03541_not_prime : ¬(recordGapCenter - 93538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93538]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03542_not_prime : ¬(recordGapCenter - 93358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93358]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03543_not_prime : ¬(recordGapCenter - 93312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93312]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03544_not_prime : ¬(recordGapCenter - 93202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93202]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03545_not_prime : ¬(recordGapCenter - 93022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 93022]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03546_not_prime : ¬(recordGapCenter - 92914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92914]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03547_not_prime : ¬(recordGapCenter - 92698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92698]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03548_not_prime : ¬(recordGapCenter - 92614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92614]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03549_not_prime : ¬(recordGapCenter - 92398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92398]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03550_not_prime : ¬(recordGapCenter - 92374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92374]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03551_not_prime : ¬(recordGapCenter - 92182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92182]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03552_not_prime : ¬(recordGapCenter - 92160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92160]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03553_not_prime : ¬(recordGapCenter - 92098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 92098]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03554_not_prime : ¬(recordGapCenter - 91774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 91774]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03555_not_prime : ¬(recordGapCenter - 91738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 91738]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03556_not_prime : ¬(recordGapCenter - 91654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 91654]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03557_not_prime : ¬(recordGapCenter - 91534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 91534]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03558_not_prime : ¬(recordGapCenter - 91138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 91138]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03559_not_prime : ¬(recordGapCenter - 91114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 91114]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03560_not_prime : ¬(recordGapCenter - 90778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90778]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03561_not_prime : ¬(recordGapCenter - 90720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90720]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03562_not_prime : ¬(recordGapCenter - 90634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90634]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03563_not_prime : ¬(recordGapCenter - 90562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90562]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03564_not_prime : ¬(recordGapCenter - 90382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90382]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03565_not_prime : ¬(recordGapCenter - 90274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90274]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03566_not_prime : ¬(recordGapCenter - 90262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 90262]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03567_not_prime : ¬(recordGapCenter - 89878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89878]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03568_not_prime : ¬(recordGapCenter - 89758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89758]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03569_not_prime : ¬(recordGapCenter - 89638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89638]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03570_not_prime : ¬(recordGapCenter - 89578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89578]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03571_not_prime : ¬(recordGapCenter - 89542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89542]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03572_not_prime : ¬(recordGapCenter - 89422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89422]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03573_not_prime : ¬(recordGapCenter - 89374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89374]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03574_not_prime : ¬(recordGapCenter - 89100).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89100]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03575_not_prime : ¬(recordGapCenter - 89098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89098]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03576_not_prime : ¬(recordGapCenter - 89014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 89014]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03577_not_prime : ¬(recordGapCenter - 88762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88762]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03578_not_prime : ¬(recordGapCenter - 88704).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88704]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03579_not_prime : ¬(recordGapCenter - 88702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88702]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03580_not_prime : ¬(recordGapCenter - 88498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88498]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03581_not_prime : ¬(recordGapCenter - 88414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88414]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03582_not_prime : ¬(recordGapCenter - 88402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88402]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03583_not_prime : ¬(recordGapCenter - 88342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88342]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

theorem fullRecordGapTerm03584_not_prime : ¬(recordGapCenter - 88042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 88042]
  · apply fullRecordGapRow00014_fermat
    simp [fullRecordGapRow00014_values]

end PrimeFactorUnimodality
