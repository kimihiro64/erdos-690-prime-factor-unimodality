import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00005_values : List Nat :=
  [fullRecordGapCenterValue - 374434,
    fullRecordGapCenterValue - 374278,
    fullRecordGapCenterValue - 374254,
    fullRecordGapCenterValue - 374182,
    fullRecordGapCenterValue - 374098,
    fullRecordGapCenterValue - 373972,
    fullRecordGapCenterValue - 373852,
    fullRecordGapCenterValue - 373818,
    fullRecordGapCenterValue - 373782,
    fullRecordGapCenterValue - 373624,
    fullRecordGapCenterValue - 373522,
    fullRecordGapCenterValue - 373398,
    fullRecordGapCenterValue - 373294,
    fullRecordGapCenterValue - 373162,
    fullRecordGapCenterValue - 373134,
    fullRecordGapCenterValue - 373012,
    fullRecordGapCenterValue - 372958,
    fullRecordGapCenterValue - 372874,
    fullRecordGapCenterValue - 372858,
    fullRecordGapCenterValue - 372754,
    fullRecordGapCenterValue - 372748,
    fullRecordGapCenterValue - 372634,
    fullRecordGapCenterValue - 372622,
    fullRecordGapCenterValue - 372594,
    fullRecordGapCenterValue - 372454,
    fullRecordGapCenterValue - 372342,
    fullRecordGapCenterValue - 372322,
    fullRecordGapCenterValue - 372238,
    fullRecordGapCenterValue - 372234,
    fullRecordGapCenterValue - 372102,
    fullRecordGapCenterValue - 372018,
    fullRecordGapCenterValue - 372004,
    fullRecordGapCenterValue - 371922,
    fullRecordGapCenterValue - 371662,
    fullRecordGapCenterValue - 371608,
    fullRecordGapCenterValue - 371578,
    fullRecordGapCenterValue - 371494,
    fullRecordGapCenterValue - 371250,
    fullRecordGapCenterValue - 371242,
    fullRecordGapCenterValue - 371062,
    fullRecordGapCenterValue - 371058,
    fullRecordGapCenterValue - 370914,
    fullRecordGapCenterValue - 370654,
    fullRecordGapCenterValue - 370618,
    fullRecordGapCenterValue - 370564,
    fullRecordGapCenterValue - 370542,
    fullRecordGapCenterValue - 370534,
    fullRecordGapCenterValue - 370492,
    fullRecordGapCenterValue - 370354,
    fullRecordGapCenterValue - 370218,
    fullRecordGapCenterValue - 370114,
    fullRecordGapCenterValue - 370102,
    fullRecordGapCenterValue - 370054,
    fullRecordGapCenterValue - 370012,
    fullRecordGapCenterValue - 369994,
    fullRecordGapCenterValue - 369654,
    fullRecordGapCenterValue - 369618,
    fullRecordGapCenterValue - 369600,
    fullRecordGapCenterValue - 369532,
    fullRecordGapCenterValue - 369508,
    fullRecordGapCenterValue - 369498,
    fullRecordGapCenterValue - 369388,
    fullRecordGapCenterValue - 369268,
    fullRecordGapCenterValue - 369214,
    fullRecordGapCenterValue - 369154,
    fullRecordGapCenterValue - 369114,
    fullRecordGapCenterValue - 369022,
    fullRecordGapCenterValue - 368974,
    fullRecordGapCenterValue - 368818,
    fullRecordGapCenterValue - 368778,
    fullRecordGapCenterValue - 368692,
    fullRecordGapCenterValue - 368674,
    fullRecordGapCenterValue - 368584,
    fullRecordGapCenterValue - 368518,
    fullRecordGapCenterValue - 368422,
    fullRecordGapCenterValue - 368398,
    fullRecordGapCenterValue - 368374,
    fullRecordGapCenterValue - 368332,
    fullRecordGapCenterValue - 368314,
    fullRecordGapCenterValue - 368308,
    fullRecordGapCenterValue - 368164,
    fullRecordGapCenterValue - 368062,
    fullRecordGapCenterValue - 368058,
    fullRecordGapCenterValue - 368034,
    fullRecordGapCenterValue - 368014,
    fullRecordGapCenterValue - 367918,
    fullRecordGapCenterValue - 367912,
    fullRecordGapCenterValue - 367762,
    fullRecordGapCenterValue - 367672,
    fullRecordGapCenterValue - 367594,
    fullRecordGapCenterValue - 367204,
    fullRecordGapCenterValue - 367084,
    fullRecordGapCenterValue - 367012,
    fullRecordGapCenterValue - 366994,
    fullRecordGapCenterValue - 366922,
    fullRecordGapCenterValue - 366844,
    fullRecordGapCenterValue - 366774,
    fullRecordGapCenterValue - 366594,
    fullRecordGapCenterValue - 366382,
    fullRecordGapCenterValue - 366342,
    fullRecordGapCenterValue - 366232,
    fullRecordGapCenterValue - 366162,
    fullRecordGapCenterValue - 366082,
    fullRecordGapCenterValue - 366042,
    fullRecordGapCenterValue - 365998,
    fullRecordGapCenterValue - 365962,
    fullRecordGapCenterValue - 365572,
    fullRecordGapCenterValue - 365538,
    fullRecordGapCenterValue - 365502,
    fullRecordGapCenterValue - 365374,
    fullRecordGapCenterValue - 365322,
    fullRecordGapCenterValue - 365278,
    fullRecordGapCenterValue - 365214,
    fullRecordGapCenterValue - 365188,
    fullRecordGapCenterValue - 365098,
    fullRecordGapCenterValue - 364972,
    fullRecordGapCenterValue - 364948,
    fullRecordGapCenterValue - 364674,
    fullRecordGapCenterValue - 364618,
    fullRecordGapCenterValue - 364552,
    fullRecordGapCenterValue - 364542,
    fullRecordGapCenterValue - 364422,
    fullRecordGapCenterValue - 364222,
    fullRecordGapCenterValue - 364198,
    fullRecordGapCenterValue - 364054,
    fullRecordGapCenterValue - 364024,
    fullRecordGapCenterValue - 363954,
    fullRecordGapCenterValue - 363934,
    fullRecordGapCenterValue - 363894,
    fullRecordGapCenterValue - 363838,
    fullRecordGapCenterValue - 363778,
    fullRecordGapCenterValue - 363604,
    fullRecordGapCenterValue - 363502,
    fullRecordGapCenterValue - 363388,
    fullRecordGapCenterValue - 363304,
    fullRecordGapCenterValue - 363172,
    fullRecordGapCenterValue - 363162,
    fullRecordGapCenterValue - 362998,
    fullRecordGapCenterValue - 362794,
    fullRecordGapCenterValue - 362728,
    fullRecordGapCenterValue - 362694,
    fullRecordGapCenterValue - 362632,
    fullRecordGapCenterValue - 362602,
    fullRecordGapCenterValue - 362562,
    fullRecordGapCenterValue - 362554,
    fullRecordGapCenterValue - 362478,
    fullRecordGapCenterValue - 362422,
    fullRecordGapCenterValue - 362382,
    fullRecordGapCenterValue - 362248,
    fullRecordGapCenterValue - 362238,
    fullRecordGapCenterValue - 362022,
    fullRecordGapCenterValue - 361918,
    fullRecordGapCenterValue - 361902,
    fullRecordGapCenterValue - 361554,
    fullRecordGapCenterValue - 361542,
    fullRecordGapCenterValue - 361462,
    fullRecordGapCenterValue - 361302,
    fullRecordGapCenterValue - 361234,
    fullRecordGapCenterValue - 361084,
    fullRecordGapCenterValue - 360988,
    fullRecordGapCenterValue - 360762,
    fullRecordGapCenterValue - 360748,
    fullRecordGapCenterValue - 360652,
    fullRecordGapCenterValue - 360642,
    fullRecordGapCenterValue - 360534,
    fullRecordGapCenterValue - 360448,
    fullRecordGapCenterValue - 360442,
    fullRecordGapCenterValue - 360292,
    fullRecordGapCenterValue - 360268,
    fullRecordGapCenterValue - 360222,
    fullRecordGapCenterValue - 360154,
    fullRecordGapCenterValue - 360124,
    fullRecordGapCenterValue - 359998,
    fullRecordGapCenterValue - 359938,
    fullRecordGapCenterValue - 359914,
    fullRecordGapCenterValue - 359908,
    fullRecordGapCenterValue - 359692,
    fullRecordGapCenterValue - 359614,
    fullRecordGapCenterValue - 359182,
    fullRecordGapCenterValue - 359068,
    fullRecordGapCenterValue - 358942,
    fullRecordGapCenterValue - 358854,
    fullRecordGapCenterValue - 358762,
    fullRecordGapCenterValue - 358738,
    fullRecordGapCenterValue - 358684,
    fullRecordGapCenterValue - 358642,
    fullRecordGapCenterValue - 358522,
    fullRecordGapCenterValue - 358482,
    fullRecordGapCenterValue - 358458,
    fullRecordGapCenterValue - 358444,
    fullRecordGapCenterValue - 358374,
    fullRecordGapCenterValue - 358312,
    fullRecordGapCenterValue - 358222,
    fullRecordGapCenterValue - 358108,
    fullRecordGapCenterValue - 358042,
    fullRecordGapCenterValue - 357772,
    fullRecordGapCenterValue - 357762,
    fullRecordGapCenterValue - 357718,
    fullRecordGapCenterValue - 357402,
    fullRecordGapCenterValue - 357342,
    fullRecordGapCenterValue - 357268,
    fullRecordGapCenterValue - 357234,
    fullRecordGapCenterValue - 357208,
    fullRecordGapCenterValue - 357202,
    fullRecordGapCenterValue - 356982,
    fullRecordGapCenterValue - 356974,
    fullRecordGapCenterValue - 356962,
    fullRecordGapCenterValue - 356838,
    fullRecordGapCenterValue - 356802,
    fullRecordGapCenterValue - 356722,
    fullRecordGapCenterValue - 356718,
    fullRecordGapCenterValue - 356614,
    fullRecordGapCenterValue - 356502,
    fullRecordGapCenterValue - 356494,
    fullRecordGapCenterValue - 356400,
    fullRecordGapCenterValue - 356394,
    fullRecordGapCenterValue - 356374,
    fullRecordGapCenterValue - 356262,
    fullRecordGapCenterValue - 356248,
    fullRecordGapCenterValue - 356214,
    fullRecordGapCenterValue - 356164,
    fullRecordGapCenterValue - 356142,
    fullRecordGapCenterValue - 356002,
    fullRecordGapCenterValue - 355998,
    fullRecordGapCenterValue - 355864,
    fullRecordGapCenterValue - 355858,
    fullRecordGapCenterValue - 355582,
    fullRecordGapCenterValue - 355492,
    fullRecordGapCenterValue - 355444,
    fullRecordGapCenterValue - 355434,
    fullRecordGapCenterValue - 355294,
    fullRecordGapCenterValue - 355254,
    fullRecordGapCenterValue - 355252,
    fullRecordGapCenterValue - 355242,
    fullRecordGapCenterValue - 355228,
    fullRecordGapCenterValue - 355098,
    fullRecordGapCenterValue - 355078,
    fullRecordGapCenterValue - 354988,
    fullRecordGapCenterValue - 354808,
    fullRecordGapCenterValue - 354724,
    fullRecordGapCenterValue - 354652,
    fullRecordGapCenterValue - 354604,
    fullRecordGapCenterValue - 354538,
    fullRecordGapCenterValue - 354478,
    fullRecordGapCenterValue - 354378,
    fullRecordGapCenterValue - 354364,
    fullRecordGapCenterValue - 354294,
    fullRecordGapCenterValue - 354232,
    fullRecordGapCenterValue - 354202,
    fullRecordGapCenterValue - 354184,
    fullRecordGapCenterValue - 354174,
    fullRecordGapCenterValue - 354052,
    fullRecordGapCenterValue - 353902,
    fullRecordGapCenterValue - 353692,
    fullRecordGapCenterValue - 353638,
    fullRecordGapCenterValue - 353512]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00005_fermat : ∀ n ∈ fullRecordGapRow00005_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01025_not_prime : ¬(recordGapCenter - 374434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374434]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01026_not_prime : ¬(recordGapCenter - 374278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374278]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01027_not_prime : ¬(recordGapCenter - 374254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374254]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01028_not_prime : ¬(recordGapCenter - 374182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374182]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01029_not_prime : ¬(recordGapCenter - 374098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 374098]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01030_not_prime : ¬(recordGapCenter - 373972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373972]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01031_not_prime : ¬(recordGapCenter - 373852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373852]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01032_not_prime : ¬(recordGapCenter - 373818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373818]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01033_not_prime : ¬(recordGapCenter - 373782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373782]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01034_not_prime : ¬(recordGapCenter - 373624).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373624]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01035_not_prime : ¬(recordGapCenter - 373522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373522]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01036_not_prime : ¬(recordGapCenter - 373398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373398]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01037_not_prime : ¬(recordGapCenter - 373294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373294]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01038_not_prime : ¬(recordGapCenter - 373162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373162]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01039_not_prime : ¬(recordGapCenter - 373134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373134]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01040_not_prime : ¬(recordGapCenter - 373012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 373012]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01041_not_prime : ¬(recordGapCenter - 372958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372958]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01042_not_prime : ¬(recordGapCenter - 372874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372874]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01043_not_prime : ¬(recordGapCenter - 372858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372858]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01044_not_prime : ¬(recordGapCenter - 372754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372754]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01045_not_prime : ¬(recordGapCenter - 372748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372748]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01046_not_prime : ¬(recordGapCenter - 372634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372634]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01047_not_prime : ¬(recordGapCenter - 372622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372622]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01048_not_prime : ¬(recordGapCenter - 372594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372594]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01049_not_prime : ¬(recordGapCenter - 372454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372454]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01050_not_prime : ¬(recordGapCenter - 372342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372342]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01051_not_prime : ¬(recordGapCenter - 372322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372322]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01052_not_prime : ¬(recordGapCenter - 372238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372238]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01053_not_prime : ¬(recordGapCenter - 372234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372234]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01054_not_prime : ¬(recordGapCenter - 372102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372102]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01055_not_prime : ¬(recordGapCenter - 372018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372018]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01056_not_prime : ¬(recordGapCenter - 372004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 372004]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01057_not_prime : ¬(recordGapCenter - 371922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371922]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01058_not_prime : ¬(recordGapCenter - 371662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371662]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01059_not_prime : ¬(recordGapCenter - 371608).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371608]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01060_not_prime : ¬(recordGapCenter - 371578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371578]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01061_not_prime : ¬(recordGapCenter - 371494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371494]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01062_not_prime : ¬(recordGapCenter - 371250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371250]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01063_not_prime : ¬(recordGapCenter - 371242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371242]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01064_not_prime : ¬(recordGapCenter - 371062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371062]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01065_not_prime : ¬(recordGapCenter - 371058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 371058]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01066_not_prime : ¬(recordGapCenter - 370914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370914]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01067_not_prime : ¬(recordGapCenter - 370654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370654]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01068_not_prime : ¬(recordGapCenter - 370618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370618]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01069_not_prime : ¬(recordGapCenter - 370564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370564]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01070_not_prime : ¬(recordGapCenter - 370542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370542]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01071_not_prime : ¬(recordGapCenter - 370534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370534]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01072_not_prime : ¬(recordGapCenter - 370492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370492]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01073_not_prime : ¬(recordGapCenter - 370354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370354]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01074_not_prime : ¬(recordGapCenter - 370218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370218]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01075_not_prime : ¬(recordGapCenter - 370114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370114]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01076_not_prime : ¬(recordGapCenter - 370102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370102]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01077_not_prime : ¬(recordGapCenter - 370054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370054]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01078_not_prime : ¬(recordGapCenter - 370012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 370012]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01079_not_prime : ¬(recordGapCenter - 369994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369994]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01080_not_prime : ¬(recordGapCenter - 369654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369654]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01081_not_prime : ¬(recordGapCenter - 369618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369618]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01082_not_prime : ¬(recordGapCenter - 369600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369600]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01083_not_prime : ¬(recordGapCenter - 369532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369532]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01084_not_prime : ¬(recordGapCenter - 369508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369508]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01085_not_prime : ¬(recordGapCenter - 369498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369498]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01086_not_prime : ¬(recordGapCenter - 369388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369388]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01087_not_prime : ¬(recordGapCenter - 369268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369268]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01088_not_prime : ¬(recordGapCenter - 369214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369214]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01089_not_prime : ¬(recordGapCenter - 369154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369154]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01090_not_prime : ¬(recordGapCenter - 369114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369114]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01091_not_prime : ¬(recordGapCenter - 369022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 369022]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01092_not_prime : ¬(recordGapCenter - 368974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368974]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01093_not_prime : ¬(recordGapCenter - 368818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368818]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01094_not_prime : ¬(recordGapCenter - 368778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368778]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01095_not_prime : ¬(recordGapCenter - 368692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368692]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01096_not_prime : ¬(recordGapCenter - 368674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368674]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01097_not_prime : ¬(recordGapCenter - 368584).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368584]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01098_not_prime : ¬(recordGapCenter - 368518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368518]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01099_not_prime : ¬(recordGapCenter - 368422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368422]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01100_not_prime : ¬(recordGapCenter - 368398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368398]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01101_not_prime : ¬(recordGapCenter - 368374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368374]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01102_not_prime : ¬(recordGapCenter - 368332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368332]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01103_not_prime : ¬(recordGapCenter - 368314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368314]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01104_not_prime : ¬(recordGapCenter - 368308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368308]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01105_not_prime : ¬(recordGapCenter - 368164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368164]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01106_not_prime : ¬(recordGapCenter - 368062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368062]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01107_not_prime : ¬(recordGapCenter - 368058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368058]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01108_not_prime : ¬(recordGapCenter - 368034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368034]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01109_not_prime : ¬(recordGapCenter - 368014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 368014]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01110_not_prime : ¬(recordGapCenter - 367918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367918]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01111_not_prime : ¬(recordGapCenter - 367912).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367912]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01112_not_prime : ¬(recordGapCenter - 367762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367762]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01113_not_prime : ¬(recordGapCenter - 367672).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367672]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01114_not_prime : ¬(recordGapCenter - 367594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367594]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01115_not_prime : ¬(recordGapCenter - 367204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367204]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01116_not_prime : ¬(recordGapCenter - 367084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367084]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01117_not_prime : ¬(recordGapCenter - 367012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 367012]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01118_not_prime : ¬(recordGapCenter - 366994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366994]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01119_not_prime : ¬(recordGapCenter - 366922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366922]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01120_not_prime : ¬(recordGapCenter - 366844).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366844]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01121_not_prime : ¬(recordGapCenter - 366774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366774]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01122_not_prime : ¬(recordGapCenter - 366594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366594]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01123_not_prime : ¬(recordGapCenter - 366382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366382]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01124_not_prime : ¬(recordGapCenter - 366342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366342]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01125_not_prime : ¬(recordGapCenter - 366232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366232]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01126_not_prime : ¬(recordGapCenter - 366162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366162]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01127_not_prime : ¬(recordGapCenter - 366082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366082]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01128_not_prime : ¬(recordGapCenter - 366042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 366042]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01129_not_prime : ¬(recordGapCenter - 365998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365998]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01130_not_prime : ¬(recordGapCenter - 365962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365962]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01131_not_prime : ¬(recordGapCenter - 365572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365572]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01132_not_prime : ¬(recordGapCenter - 365538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365538]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01133_not_prime : ¬(recordGapCenter - 365502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365502]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01134_not_prime : ¬(recordGapCenter - 365374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365374]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01135_not_prime : ¬(recordGapCenter - 365322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365322]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01136_not_prime : ¬(recordGapCenter - 365278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365278]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01137_not_prime : ¬(recordGapCenter - 365214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365214]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01138_not_prime : ¬(recordGapCenter - 365188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365188]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01139_not_prime : ¬(recordGapCenter - 365098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 365098]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01140_not_prime : ¬(recordGapCenter - 364972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364972]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01141_not_prime : ¬(recordGapCenter - 364948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364948]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01142_not_prime : ¬(recordGapCenter - 364674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364674]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01143_not_prime : ¬(recordGapCenter - 364618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364618]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01144_not_prime : ¬(recordGapCenter - 364552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364552]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01145_not_prime : ¬(recordGapCenter - 364542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364542]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01146_not_prime : ¬(recordGapCenter - 364422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364422]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01147_not_prime : ¬(recordGapCenter - 364222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364222]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01148_not_prime : ¬(recordGapCenter - 364198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364198]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01149_not_prime : ¬(recordGapCenter - 364054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364054]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01150_not_prime : ¬(recordGapCenter - 364024).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 364024]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01151_not_prime : ¬(recordGapCenter - 363954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363954]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01152_not_prime : ¬(recordGapCenter - 363934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363934]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01153_not_prime : ¬(recordGapCenter - 363894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363894]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01154_not_prime : ¬(recordGapCenter - 363838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363838]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01155_not_prime : ¬(recordGapCenter - 363778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363778]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01156_not_prime : ¬(recordGapCenter - 363604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363604]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01157_not_prime : ¬(recordGapCenter - 363502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363502]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01158_not_prime : ¬(recordGapCenter - 363388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363388]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01159_not_prime : ¬(recordGapCenter - 363304).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363304]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01160_not_prime : ¬(recordGapCenter - 363172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363172]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01161_not_prime : ¬(recordGapCenter - 363162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 363162]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01162_not_prime : ¬(recordGapCenter - 362998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362998]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01163_not_prime : ¬(recordGapCenter - 362794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362794]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01164_not_prime : ¬(recordGapCenter - 362728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362728]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01165_not_prime : ¬(recordGapCenter - 362694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362694]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01166_not_prime : ¬(recordGapCenter - 362632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362632]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01167_not_prime : ¬(recordGapCenter - 362602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362602]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01168_not_prime : ¬(recordGapCenter - 362562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362562]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01169_not_prime : ¬(recordGapCenter - 362554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362554]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01170_not_prime : ¬(recordGapCenter - 362478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362478]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01171_not_prime : ¬(recordGapCenter - 362422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362422]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01172_not_prime : ¬(recordGapCenter - 362382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362382]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01173_not_prime : ¬(recordGapCenter - 362248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362248]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01174_not_prime : ¬(recordGapCenter - 362238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362238]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01175_not_prime : ¬(recordGapCenter - 362022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 362022]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01176_not_prime : ¬(recordGapCenter - 361918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361918]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01177_not_prime : ¬(recordGapCenter - 361902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361902]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01178_not_prime : ¬(recordGapCenter - 361554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361554]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01179_not_prime : ¬(recordGapCenter - 361542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361542]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01180_not_prime : ¬(recordGapCenter - 361462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361462]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01181_not_prime : ¬(recordGapCenter - 361302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361302]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01182_not_prime : ¬(recordGapCenter - 361234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361234]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01183_not_prime : ¬(recordGapCenter - 361084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 361084]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01184_not_prime : ¬(recordGapCenter - 360988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360988]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01185_not_prime : ¬(recordGapCenter - 360762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360762]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01186_not_prime : ¬(recordGapCenter - 360748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360748]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01187_not_prime : ¬(recordGapCenter - 360652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360652]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01188_not_prime : ¬(recordGapCenter - 360642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360642]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01189_not_prime : ¬(recordGapCenter - 360534).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360534]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01190_not_prime : ¬(recordGapCenter - 360448).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360448]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01191_not_prime : ¬(recordGapCenter - 360442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360442]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01192_not_prime : ¬(recordGapCenter - 360292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360292]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01193_not_prime : ¬(recordGapCenter - 360268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360268]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01194_not_prime : ¬(recordGapCenter - 360222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360222]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01195_not_prime : ¬(recordGapCenter - 360154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360154]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01196_not_prime : ¬(recordGapCenter - 360124).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 360124]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01197_not_prime : ¬(recordGapCenter - 359998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359998]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01198_not_prime : ¬(recordGapCenter - 359938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359938]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01199_not_prime : ¬(recordGapCenter - 359914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359914]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01200_not_prime : ¬(recordGapCenter - 359908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359908]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01201_not_prime : ¬(recordGapCenter - 359692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359692]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01202_not_prime : ¬(recordGapCenter - 359614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359614]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01203_not_prime : ¬(recordGapCenter - 359182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359182]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01204_not_prime : ¬(recordGapCenter - 359068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 359068]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01205_not_prime : ¬(recordGapCenter - 358942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358942]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01206_not_prime : ¬(recordGapCenter - 358854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358854]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01207_not_prime : ¬(recordGapCenter - 358762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358762]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01208_not_prime : ¬(recordGapCenter - 358738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358738]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01209_not_prime : ¬(recordGapCenter - 358684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358684]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01210_not_prime : ¬(recordGapCenter - 358642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358642]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01211_not_prime : ¬(recordGapCenter - 358522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358522]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01212_not_prime : ¬(recordGapCenter - 358482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358482]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01213_not_prime : ¬(recordGapCenter - 358458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358458]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01214_not_prime : ¬(recordGapCenter - 358444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358444]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01215_not_prime : ¬(recordGapCenter - 358374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358374]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01216_not_prime : ¬(recordGapCenter - 358312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358312]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01217_not_prime : ¬(recordGapCenter - 358222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358222]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01218_not_prime : ¬(recordGapCenter - 358108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358108]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01219_not_prime : ¬(recordGapCenter - 358042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 358042]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01220_not_prime : ¬(recordGapCenter - 357772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357772]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01221_not_prime : ¬(recordGapCenter - 357762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357762]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01222_not_prime : ¬(recordGapCenter - 357718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357718]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01223_not_prime : ¬(recordGapCenter - 357402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357402]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01224_not_prime : ¬(recordGapCenter - 357342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357342]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01225_not_prime : ¬(recordGapCenter - 357268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357268]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01226_not_prime : ¬(recordGapCenter - 357234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357234]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01227_not_prime : ¬(recordGapCenter - 357208).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357208]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01228_not_prime : ¬(recordGapCenter - 357202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 357202]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01229_not_prime : ¬(recordGapCenter - 356982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356982]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01230_not_prime : ¬(recordGapCenter - 356974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356974]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01231_not_prime : ¬(recordGapCenter - 356962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356962]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01232_not_prime : ¬(recordGapCenter - 356838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356838]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01233_not_prime : ¬(recordGapCenter - 356802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356802]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01234_not_prime : ¬(recordGapCenter - 356722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356722]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01235_not_prime : ¬(recordGapCenter - 356718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356718]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01236_not_prime : ¬(recordGapCenter - 356614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356614]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01237_not_prime : ¬(recordGapCenter - 356502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356502]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01238_not_prime : ¬(recordGapCenter - 356494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356494]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01239_not_prime : ¬(recordGapCenter - 356400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356400]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01240_not_prime : ¬(recordGapCenter - 356394).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356394]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01241_not_prime : ¬(recordGapCenter - 356374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356374]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01242_not_prime : ¬(recordGapCenter - 356262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356262]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01243_not_prime : ¬(recordGapCenter - 356248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356248]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01244_not_prime : ¬(recordGapCenter - 356214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356214]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01245_not_prime : ¬(recordGapCenter - 356164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356164]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01246_not_prime : ¬(recordGapCenter - 356142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356142]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01247_not_prime : ¬(recordGapCenter - 356002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 356002]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01248_not_prime : ¬(recordGapCenter - 355998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355998]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01249_not_prime : ¬(recordGapCenter - 355864).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355864]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01250_not_prime : ¬(recordGapCenter - 355858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355858]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01251_not_prime : ¬(recordGapCenter - 355582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355582]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01252_not_prime : ¬(recordGapCenter - 355492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355492]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01253_not_prime : ¬(recordGapCenter - 355444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355444]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01254_not_prime : ¬(recordGapCenter - 355434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355434]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01255_not_prime : ¬(recordGapCenter - 355294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355294]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01256_not_prime : ¬(recordGapCenter - 355254).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355254]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01257_not_prime : ¬(recordGapCenter - 355252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355252]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01258_not_prime : ¬(recordGapCenter - 355242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355242]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01259_not_prime : ¬(recordGapCenter - 355228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355228]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01260_not_prime : ¬(recordGapCenter - 355098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355098]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01261_not_prime : ¬(recordGapCenter - 355078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 355078]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01262_not_prime : ¬(recordGapCenter - 354988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354988]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01263_not_prime : ¬(recordGapCenter - 354808).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354808]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01264_not_prime : ¬(recordGapCenter - 354724).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354724]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01265_not_prime : ¬(recordGapCenter - 354652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354652]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01266_not_prime : ¬(recordGapCenter - 354604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354604]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01267_not_prime : ¬(recordGapCenter - 354538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354538]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01268_not_prime : ¬(recordGapCenter - 354478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354478]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01269_not_prime : ¬(recordGapCenter - 354378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354378]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01270_not_prime : ¬(recordGapCenter - 354364).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354364]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01271_not_prime : ¬(recordGapCenter - 354294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354294]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01272_not_prime : ¬(recordGapCenter - 354232).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354232]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01273_not_prime : ¬(recordGapCenter - 354202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354202]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01274_not_prime : ¬(recordGapCenter - 354184).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354184]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01275_not_prime : ¬(recordGapCenter - 354174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354174]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01276_not_prime : ¬(recordGapCenter - 354052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 354052]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01277_not_prime : ¬(recordGapCenter - 353902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353902]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01278_not_prime : ¬(recordGapCenter - 353692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353692]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01279_not_prime : ¬(recordGapCenter - 353638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353638]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

theorem fullRecordGapTerm01280_not_prime : ¬(recordGapCenter - 353512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 353512]
  · apply fullRecordGapRow00005_fermat
    simp [fullRecordGapRow00005_values]

end PrimeFactorUnimodality
