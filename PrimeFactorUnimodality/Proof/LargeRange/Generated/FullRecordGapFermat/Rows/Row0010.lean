import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00010_values : List Nat :=
  [fullRecordGapCenterValue - 264742,
    fullRecordGapCenterValue - 264714,
    fullRecordGapCenterValue - 264600,
    fullRecordGapCenterValue - 264514,
    fullRecordGapCenterValue - 264274,
    fullRecordGapCenterValue - 264162,
    fullRecordGapCenterValue - 264148,
    fullRecordGapCenterValue - 264142,
    fullRecordGapCenterValue - 264102,
    fullRecordGapCenterValue - 263932,
    fullRecordGapCenterValue - 263878,
    fullRecordGapCenterValue - 263854,
    fullRecordGapCenterValue - 263814,
    fullRecordGapCenterValue - 263778,
    fullRecordGapCenterValue - 263598,
    fullRecordGapCenterValue - 263554,
    fullRecordGapCenterValue - 263518,
    fullRecordGapCenterValue - 263422,
    fullRecordGapCenterValue - 263202,
    fullRecordGapCenterValue - 263182,
    fullRecordGapCenterValue - 263118,
    fullRecordGapCenterValue - 263044,
    fullRecordGapCenterValue - 262978,
    fullRecordGapCenterValue - 262954,
    fullRecordGapCenterValue - 262894,
    fullRecordGapCenterValue - 262852,
    fullRecordGapCenterValue - 262762,
    fullRecordGapCenterValue - 262722,
    fullRecordGapCenterValue - 262714,
    fullRecordGapCenterValue - 262698,
    fullRecordGapCenterValue - 262642,
    fullRecordGapCenterValue - 262594,
    fullRecordGapCenterValue - 262554,
    fullRecordGapCenterValue - 262498,
    fullRecordGapCenterValue - 262440,
    fullRecordGapCenterValue - 262348,
    fullRecordGapCenterValue - 262324,
    fullRecordGapCenterValue - 262258,
    fullRecordGapCenterValue - 262204,
    fullRecordGapCenterValue - 262084,
    fullRecordGapCenterValue - 262014,
    fullRecordGapCenterValue - 261954,
    fullRecordGapCenterValue - 261798,
    fullRecordGapCenterValue - 261762,
    fullRecordGapCenterValue - 261748,
    fullRecordGapCenterValue - 261634,
    fullRecordGapCenterValue - 261622,
    fullRecordGapCenterValue - 261582,
    fullRecordGapCenterValue - 261574,
    fullRecordGapCenterValue - 261462,
    fullRecordGapCenterValue - 261412,
    fullRecordGapCenterValue - 261292,
    fullRecordGapCenterValue - 261238,
    fullRecordGapCenterValue - 261028,
    fullRecordGapCenterValue - 260922,
    fullRecordGapCenterValue - 260878,
    fullRecordGapCenterValue - 260818,
    fullRecordGapCenterValue - 260812,
    fullRecordGapCenterValue - 260742,
    fullRecordGapCenterValue - 260614,
    fullRecordGapCenterValue - 260518,
    fullRecordGapCenterValue - 260404,
    fullRecordGapCenterValue - 260398,
    fullRecordGapCenterValue - 260382,
    fullRecordGapCenterValue - 259878,
    fullRecordGapCenterValue - 259804,
    fullRecordGapCenterValue - 259564,
    fullRecordGapCenterValue - 259342,
    fullRecordGapCenterValue - 259338,
    fullRecordGapCenterValue - 259308,
    fullRecordGapCenterValue - 259282,
    fullRecordGapCenterValue - 259132,
    fullRecordGapCenterValue - 259062,
    fullRecordGapCenterValue - 259018,
    fullRecordGapCenterValue - 258954,
    fullRecordGapCenterValue - 258898,
    fullRecordGapCenterValue - 258720,
    fullRecordGapCenterValue - 258694,
    fullRecordGapCenterValue - 258484,
    fullRecordGapCenterValue - 258418,
    fullRecordGapCenterValue - 258178,
    fullRecordGapCenterValue - 258022,
    fullRecordGapCenterValue - 257962,
    fullRecordGapCenterValue - 257878,
    fullRecordGapCenterValue - 257674,
    fullRecordGapCenterValue - 257662,
    fullRecordGapCenterValue - 257638,
    fullRecordGapCenterValue - 257434,
    fullRecordGapCenterValue - 257332,
    fullRecordGapCenterValue - 257308,
    fullRecordGapCenterValue - 257098,
    fullRecordGapCenterValue - 257038,
    fullRecordGapCenterValue - 256948,
    fullRecordGapCenterValue - 256822,
    fullRecordGapCenterValue - 256798,
    fullRecordGapCenterValue - 256702,
    fullRecordGapCenterValue - 256608,
    fullRecordGapCenterValue - 256324,
    fullRecordGapCenterValue - 256252,
    fullRecordGapCenterValue - 256198,
    fullRecordGapCenterValue - 256132,
    fullRecordGapCenterValue - 255988,
    fullRecordGapCenterValue - 255862,
    fullRecordGapCenterValue - 255628,
    fullRecordGapCenterValue - 255552,
    fullRecordGapCenterValue - 255412,
    fullRecordGapCenterValue - 254578,
    fullRecordGapCenterValue - 254482,
    fullRecordGapCenterValue - 254404,
    fullRecordGapCenterValue - 254314,
    fullRecordGapCenterValue - 254278,
    fullRecordGapCenterValue - 254074,
    fullRecordGapCenterValue - 254062,
    fullRecordGapCenterValue - 253852,
    fullRecordGapCenterValue - 253714,
    fullRecordGapCenterValue - 253684,
    fullRecordGapCenterValue - 253678,
    fullRecordGapCenterValue - 253654,
    fullRecordGapCenterValue - 253564,
    fullRecordGapCenterValue - 253468,
    fullRecordGapCenterValue - 253440,
    fullRecordGapCenterValue - 253348,
    fullRecordGapCenterValue - 253252,
    fullRecordGapCenterValue - 253222,
    fullRecordGapCenterValue - 252622,
    fullRecordGapCenterValue - 252514,
    fullRecordGapCenterValue - 252508,
    fullRecordGapCenterValue - 252412,
    fullRecordGapCenterValue - 252262,
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
    fullRecordGapCenterValue - 245452,
    fullRecordGapCenterValue - 245332,
    fullRecordGapCenterValue - 245188,
    fullRecordGapCenterValue - 244978,
    fullRecordGapCenterValue - 244944,
    fullRecordGapCenterValue - 244564,
    fullRecordGapCenterValue - 244558,
    fullRecordGapCenterValue - 244414,
    fullRecordGapCenterValue - 244234,
    fullRecordGapCenterValue - 244198,
    fullRecordGapCenterValue - 244102,
    fullRecordGapCenterValue - 244054,
    fullRecordGapCenterValue - 243778,
    fullRecordGapCenterValue - 243772,
    fullRecordGapCenterValue - 243604,
    fullRecordGapCenterValue - 243262,
    fullRecordGapCenterValue - 243172,
    fullRecordGapCenterValue - 243154,
    fullRecordGapCenterValue - 242938,
    fullRecordGapCenterValue - 242878,
    fullRecordGapCenterValue - 242842,
    fullRecordGapCenterValue - 242758,
    fullRecordGapCenterValue - 242644,
    fullRecordGapCenterValue - 242524,
    fullRecordGapCenterValue - 242458,
    fullRecordGapCenterValue - 242314,
    fullRecordGapCenterValue - 242134,
    fullRecordGapCenterValue - 242002,
    fullRecordGapCenterValue - 241920,
    fullRecordGapCenterValue - 241882,
    fullRecordGapCenterValue - 241372,
    fullRecordGapCenterValue - 241342,
    fullRecordGapCenterValue - 241294,
    fullRecordGapCenterValue - 240742,
    fullRecordGapCenterValue - 240532,
    fullRecordGapCenterValue - 240418,
    fullRecordGapCenterValue - 240412,
    fullRecordGapCenterValue - 240148,
    fullRecordGapCenterValue - 240100,
    fullRecordGapCenterValue - 240022,
    fullRecordGapCenterValue - 240000,
    fullRecordGapCenterValue - 239662,
    fullRecordGapCenterValue - 239332,
    fullRecordGapCenterValue - 239182,
    fullRecordGapCenterValue - 239164,
    fullRecordGapCenterValue - 239098,
    fullRecordGapCenterValue - 238978,
    fullRecordGapCenterValue - 238894,
    fullRecordGapCenterValue - 238828,
    fullRecordGapCenterValue - 238324,
    fullRecordGapCenterValue - 238318,
    fullRecordGapCenterValue - 237862,
    fullRecordGapCenterValue - 237814,
    fullRecordGapCenterValue - 237514,
    fullRecordGapCenterValue - 237502,
    fullRecordGapCenterValue - 237382,
    fullRecordGapCenterValue - 237160,
    fullRecordGapCenterValue - 237052,
    fullRecordGapCenterValue - 236932,
    fullRecordGapCenterValue - 236554,
    fullRecordGapCenterValue - 236544,
    fullRecordGapCenterValue - 236338,
    fullRecordGapCenterValue - 236332,
    fullRecordGapCenterValue - 236250,
    fullRecordGapCenterValue - 236212]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00010_fermat : ∀ n ∈ fullRecordGapRow00010_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02305_not_prime : ¬(recordGapCenter - 264742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264742]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02306_not_prime : ¬(recordGapCenter - 264714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264714]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02307_not_prime : ¬(recordGapCenter - 264600).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264600]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02308_not_prime : ¬(recordGapCenter - 264514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264514]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02309_not_prime : ¬(recordGapCenter - 264274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264274]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02310_not_prime : ¬(recordGapCenter - 264162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264162]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02311_not_prime : ¬(recordGapCenter - 264148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264148]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02312_not_prime : ¬(recordGapCenter - 264142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264142]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02313_not_prime : ¬(recordGapCenter - 264102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 264102]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02314_not_prime : ¬(recordGapCenter - 263932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263932]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02315_not_prime : ¬(recordGapCenter - 263878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263878]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02316_not_prime : ¬(recordGapCenter - 263854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263854]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02317_not_prime : ¬(recordGapCenter - 263814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263814]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02318_not_prime : ¬(recordGapCenter - 263778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263778]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02319_not_prime : ¬(recordGapCenter - 263598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263598]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02320_not_prime : ¬(recordGapCenter - 263554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263554]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02321_not_prime : ¬(recordGapCenter - 263518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263518]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02322_not_prime : ¬(recordGapCenter - 263422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263422]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02323_not_prime : ¬(recordGapCenter - 263202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263202]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02324_not_prime : ¬(recordGapCenter - 263182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263182]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02325_not_prime : ¬(recordGapCenter - 263118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263118]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02326_not_prime : ¬(recordGapCenter - 263044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 263044]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02327_not_prime : ¬(recordGapCenter - 262978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262978]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02328_not_prime : ¬(recordGapCenter - 262954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262954]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02329_not_prime : ¬(recordGapCenter - 262894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262894]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02330_not_prime : ¬(recordGapCenter - 262852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262852]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02331_not_prime : ¬(recordGapCenter - 262762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262762]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02332_not_prime : ¬(recordGapCenter - 262722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262722]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02333_not_prime : ¬(recordGapCenter - 262714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262714]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02334_not_prime : ¬(recordGapCenter - 262698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262698]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02335_not_prime : ¬(recordGapCenter - 262642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262642]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02336_not_prime : ¬(recordGapCenter - 262594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262594]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02337_not_prime : ¬(recordGapCenter - 262554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262554]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02338_not_prime : ¬(recordGapCenter - 262498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262498]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02339_not_prime : ¬(recordGapCenter - 262440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262440]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02340_not_prime : ¬(recordGapCenter - 262348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262348]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02341_not_prime : ¬(recordGapCenter - 262324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262324]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02342_not_prime : ¬(recordGapCenter - 262258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262258]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02343_not_prime : ¬(recordGapCenter - 262204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262204]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02344_not_prime : ¬(recordGapCenter - 262084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262084]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02345_not_prime : ¬(recordGapCenter - 262014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 262014]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02346_not_prime : ¬(recordGapCenter - 261954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261954]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02347_not_prime : ¬(recordGapCenter - 261798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261798]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02348_not_prime : ¬(recordGapCenter - 261762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261762]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02349_not_prime : ¬(recordGapCenter - 261748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261748]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02350_not_prime : ¬(recordGapCenter - 261634).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261634]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02351_not_prime : ¬(recordGapCenter - 261622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261622]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02352_not_prime : ¬(recordGapCenter - 261582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261582]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02353_not_prime : ¬(recordGapCenter - 261574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261574]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02354_not_prime : ¬(recordGapCenter - 261462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261462]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02355_not_prime : ¬(recordGapCenter - 261412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261412]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02356_not_prime : ¬(recordGapCenter - 261292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261292]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02357_not_prime : ¬(recordGapCenter - 261238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261238]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02358_not_prime : ¬(recordGapCenter - 261028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 261028]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02359_not_prime : ¬(recordGapCenter - 260922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260922]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02360_not_prime : ¬(recordGapCenter - 260878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260878]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02361_not_prime : ¬(recordGapCenter - 260818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260818]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02362_not_prime : ¬(recordGapCenter - 260812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260812]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02363_not_prime : ¬(recordGapCenter - 260742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260742]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02364_not_prime : ¬(recordGapCenter - 260614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260614]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02365_not_prime : ¬(recordGapCenter - 260518).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260518]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02366_not_prime : ¬(recordGapCenter - 260404).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260404]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02367_not_prime : ¬(recordGapCenter - 260398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260398]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02368_not_prime : ¬(recordGapCenter - 260382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 260382]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02369_not_prime : ¬(recordGapCenter - 259878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259878]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02370_not_prime : ¬(recordGapCenter - 259804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259804]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02371_not_prime : ¬(recordGapCenter - 259564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259564]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02372_not_prime : ¬(recordGapCenter - 259342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259342]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02373_not_prime : ¬(recordGapCenter - 259338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259338]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02374_not_prime : ¬(recordGapCenter - 259308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259308]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02375_not_prime : ¬(recordGapCenter - 259282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259282]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02376_not_prime : ¬(recordGapCenter - 259132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259132]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02377_not_prime : ¬(recordGapCenter - 259062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259062]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02378_not_prime : ¬(recordGapCenter - 259018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 259018]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02379_not_prime : ¬(recordGapCenter - 258954).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258954]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02380_not_prime : ¬(recordGapCenter - 258898).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258898]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02381_not_prime : ¬(recordGapCenter - 258720).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258720]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02382_not_prime : ¬(recordGapCenter - 258694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258694]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02383_not_prime : ¬(recordGapCenter - 258484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258484]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02384_not_prime : ¬(recordGapCenter - 258418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258418]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02385_not_prime : ¬(recordGapCenter - 258178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258178]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02386_not_prime : ¬(recordGapCenter - 258022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 258022]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02387_not_prime : ¬(recordGapCenter - 257962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257962]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02388_not_prime : ¬(recordGapCenter - 257878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257878]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02389_not_prime : ¬(recordGapCenter - 257674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257674]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02390_not_prime : ¬(recordGapCenter - 257662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257662]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02391_not_prime : ¬(recordGapCenter - 257638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257638]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02392_not_prime : ¬(recordGapCenter - 257434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257434]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02393_not_prime : ¬(recordGapCenter - 257332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257332]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02394_not_prime : ¬(recordGapCenter - 257308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257308]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02395_not_prime : ¬(recordGapCenter - 257098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257098]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02396_not_prime : ¬(recordGapCenter - 257038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 257038]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02397_not_prime : ¬(recordGapCenter - 256948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256948]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02398_not_prime : ¬(recordGapCenter - 256822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256822]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02399_not_prime : ¬(recordGapCenter - 256798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256798]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02400_not_prime : ¬(recordGapCenter - 256702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256702]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02401_not_prime : ¬(recordGapCenter - 256608).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256608]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02402_not_prime : ¬(recordGapCenter - 256324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256324]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02403_not_prime : ¬(recordGapCenter - 256252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256252]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02404_not_prime : ¬(recordGapCenter - 256198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256198]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02405_not_prime : ¬(recordGapCenter - 256132).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 256132]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02406_not_prime : ¬(recordGapCenter - 255988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 255988]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02407_not_prime : ¬(recordGapCenter - 255862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 255862]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02408_not_prime : ¬(recordGapCenter - 255628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 255628]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02409_not_prime : ¬(recordGapCenter - 255552).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 255552]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02410_not_prime : ¬(recordGapCenter - 255412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 255412]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02411_not_prime : ¬(recordGapCenter - 254578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 254578]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02412_not_prime : ¬(recordGapCenter - 254482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 254482]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02413_not_prime : ¬(recordGapCenter - 254404).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 254404]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02414_not_prime : ¬(recordGapCenter - 254314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 254314]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02415_not_prime : ¬(recordGapCenter - 254278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 254278]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02416_not_prime : ¬(recordGapCenter - 254074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 254074]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02417_not_prime : ¬(recordGapCenter - 254062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 254062]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02418_not_prime : ¬(recordGapCenter - 253852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253852]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02419_not_prime : ¬(recordGapCenter - 253714).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253714]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02420_not_prime : ¬(recordGapCenter - 253684).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253684]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02421_not_prime : ¬(recordGapCenter - 253678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253678]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02422_not_prime : ¬(recordGapCenter - 253654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253654]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02423_not_prime : ¬(recordGapCenter - 253564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253564]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02424_not_prime : ¬(recordGapCenter - 253468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253468]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02425_not_prime : ¬(recordGapCenter - 253440).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253440]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02426_not_prime : ¬(recordGapCenter - 253348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253348]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02427_not_prime : ¬(recordGapCenter - 253252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253252]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02428_not_prime : ¬(recordGapCenter - 253222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 253222]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02429_not_prime : ¬(recordGapCenter - 252622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252622]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02430_not_prime : ¬(recordGapCenter - 252514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252514]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02431_not_prime : ¬(recordGapCenter - 252508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252508]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02432_not_prime : ¬(recordGapCenter - 252412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252412]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02433_not_prime : ¬(recordGapCenter - 252262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252262]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02434_not_prime : ¬(recordGapCenter - 252082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252082]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02435_not_prime : ¬(recordGapCenter - 252000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 252000]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02436_not_prime : ¬(recordGapCenter - 251422).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 251422]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02437_not_prime : ¬(recordGapCenter - 251374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 251374]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02438_not_prime : ¬(recordGapCenter - 251242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 251242]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02439_not_prime : ¬(recordGapCenter - 251194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 251194]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02440_not_prime : ¬(recordGapCenter - 251164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 251164]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02441_not_prime : ¬(recordGapCenter - 251092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 251092]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02442_not_prime : ¬(recordGapCenter - 251044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 251044]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02443_not_prime : ¬(recordGapCenter - 250924).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250924]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02444_not_prime : ¬(recordGapCenter - 250882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250882]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02445_not_prime : ¬(recordGapCenter - 250858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250858]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02446_not_prime : ¬(recordGapCenter - 250798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250798]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02447_not_prime : ¬(recordGapCenter - 250522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250522]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02448_not_prime : ¬(recordGapCenter - 250462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250462]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02449_not_prime : ¬(recordGapCenter - 250414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250414]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02450_not_prime : ¬(recordGapCenter - 250402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250402]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02451_not_prime : ¬(recordGapCenter - 250000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 250000]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02452_not_prime : ¬(recordGapCenter - 249988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 249988]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02453_not_prime : ¬(recordGapCenter - 249982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 249982]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02454_not_prime : ¬(recordGapCenter - 249598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 249598]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02455_not_prime : ¬(recordGapCenter - 249538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 249538]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02456_not_prime : ¬(recordGapCenter - 249532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 249532]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02457_not_prime : ¬(recordGapCenter - 249478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 249478]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02458_not_prime : ¬(recordGapCenter - 249388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 249388]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02459_not_prime : ¬(recordGapCenter - 248932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248932]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02460_not_prime : ¬(recordGapCenter - 248764).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248764]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02461_not_prime : ¬(recordGapCenter - 248734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248734]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02462_not_prime : ¬(recordGapCenter - 248674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248674]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02463_not_prime : ¬(recordGapCenter - 248602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248602]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02464_not_prime : ¬(recordGapCenter - 248554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248554]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02465_not_prime : ¬(recordGapCenter - 248278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248278]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02466_not_prime : ¬(recordGapCenter - 248194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248194]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02467_not_prime : ¬(recordGapCenter - 248134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248134]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02468_not_prime : ¬(recordGapCenter - 248068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248068]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02469_not_prime : ¬(recordGapCenter - 248044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 248044]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02470_not_prime : ¬(recordGapCenter - 247774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 247774]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02471_not_prime : ¬(recordGapCenter - 247732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 247732]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02472_not_prime : ¬(recordGapCenter - 247642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 247642]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02473_not_prime : ¬(recordGapCenter - 247582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 247582]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02474_not_prime : ¬(recordGapCenter - 247474).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 247474]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02475_not_prime : ¬(recordGapCenter - 247348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 247348]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02476_not_prime : ¬(recordGapCenter - 246838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246838]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02477_not_prime : ¬(recordGapCenter - 246802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246802]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02478_not_prime : ¬(recordGapCenter - 246754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246754]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02479_not_prime : ¬(recordGapCenter - 246628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246628]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02480_not_prime : ¬(recordGapCenter - 246622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246622]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02481_not_prime : ¬(recordGapCenter - 246538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246538]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02482_not_prime : ¬(recordGapCenter - 246508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246508]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02483_not_prime : ¬(recordGapCenter - 246418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246418]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02484_not_prime : ¬(recordGapCenter - 246412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246412]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02485_not_prime : ¬(recordGapCenter - 246400).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246400]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02486_not_prime : ¬(recordGapCenter - 246244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246244]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02487_not_prime : ¬(recordGapCenter - 246172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246172]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02488_not_prime : ¬(recordGapCenter - 246154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 246154]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02489_not_prime : ¬(recordGapCenter - 245914).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245914]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02490_not_prime : ¬(recordGapCenter - 245884).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245884]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02491_not_prime : ¬(recordGapCenter - 245878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245878]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02492_not_prime : ¬(recordGapCenter - 245782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245782]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02493_not_prime : ¬(recordGapCenter - 245760).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245760]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02494_not_prime : ¬(recordGapCenter - 245734).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245734]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02495_not_prime : ¬(recordGapCenter - 245668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245668]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02496_not_prime : ¬(recordGapCenter - 245452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245452]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02497_not_prime : ¬(recordGapCenter - 245332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245332]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02498_not_prime : ¬(recordGapCenter - 245188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 245188]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02499_not_prime : ¬(recordGapCenter - 244978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244978]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02500_not_prime : ¬(recordGapCenter - 244944).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244944]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02501_not_prime : ¬(recordGapCenter - 244564).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244564]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02502_not_prime : ¬(recordGapCenter - 244558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244558]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02503_not_prime : ¬(recordGapCenter - 244414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244414]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02504_not_prime : ¬(recordGapCenter - 244234).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244234]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02505_not_prime : ¬(recordGapCenter - 244198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244198]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02506_not_prime : ¬(recordGapCenter - 244102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244102]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02507_not_prime : ¬(recordGapCenter - 244054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 244054]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02508_not_prime : ¬(recordGapCenter - 243778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 243778]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02509_not_prime : ¬(recordGapCenter - 243772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 243772]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02510_not_prime : ¬(recordGapCenter - 243604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 243604]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02511_not_prime : ¬(recordGapCenter - 243262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 243262]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02512_not_prime : ¬(recordGapCenter - 243172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 243172]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02513_not_prime : ¬(recordGapCenter - 243154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 243154]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02514_not_prime : ¬(recordGapCenter - 242938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242938]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02515_not_prime : ¬(recordGapCenter - 242878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242878]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02516_not_prime : ¬(recordGapCenter - 242842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242842]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02517_not_prime : ¬(recordGapCenter - 242758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242758]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02518_not_prime : ¬(recordGapCenter - 242644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242644]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02519_not_prime : ¬(recordGapCenter - 242524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242524]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02520_not_prime : ¬(recordGapCenter - 242458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242458]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02521_not_prime : ¬(recordGapCenter - 242314).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242314]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02522_not_prime : ¬(recordGapCenter - 242134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242134]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02523_not_prime : ¬(recordGapCenter - 242002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 242002]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02524_not_prime : ¬(recordGapCenter - 241920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 241920]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02525_not_prime : ¬(recordGapCenter - 241882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 241882]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02526_not_prime : ¬(recordGapCenter - 241372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 241372]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02527_not_prime : ¬(recordGapCenter - 241342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 241342]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02528_not_prime : ¬(recordGapCenter - 241294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 241294]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02529_not_prime : ¬(recordGapCenter - 240742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240742]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02530_not_prime : ¬(recordGapCenter - 240532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240532]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02531_not_prime : ¬(recordGapCenter - 240418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240418]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02532_not_prime : ¬(recordGapCenter - 240412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240412]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02533_not_prime : ¬(recordGapCenter - 240148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240148]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02534_not_prime : ¬(recordGapCenter - 240100).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240100]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02535_not_prime : ¬(recordGapCenter - 240022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240022]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02536_not_prime : ¬(recordGapCenter - 240000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 240000]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02537_not_prime : ¬(recordGapCenter - 239662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 239662]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02538_not_prime : ¬(recordGapCenter - 239332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 239332]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02539_not_prime : ¬(recordGapCenter - 239182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 239182]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02540_not_prime : ¬(recordGapCenter - 239164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 239164]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02541_not_prime : ¬(recordGapCenter - 239098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 239098]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02542_not_prime : ¬(recordGapCenter - 238978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 238978]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02543_not_prime : ¬(recordGapCenter - 238894).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 238894]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02544_not_prime : ¬(recordGapCenter - 238828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 238828]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02545_not_prime : ¬(recordGapCenter - 238324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 238324]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02546_not_prime : ¬(recordGapCenter - 238318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 238318]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02547_not_prime : ¬(recordGapCenter - 237862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 237862]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02548_not_prime : ¬(recordGapCenter - 237814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 237814]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02549_not_prime : ¬(recordGapCenter - 237514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 237514]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02550_not_prime : ¬(recordGapCenter - 237502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 237502]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02551_not_prime : ¬(recordGapCenter - 237382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 237382]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02552_not_prime : ¬(recordGapCenter - 237160).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 237160]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02553_not_prime : ¬(recordGapCenter - 237052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 237052]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02554_not_prime : ¬(recordGapCenter - 236932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236932]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02555_not_prime : ¬(recordGapCenter - 236554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236554]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02556_not_prime : ¬(recordGapCenter - 236544).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236544]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02557_not_prime : ¬(recordGapCenter - 236338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236338]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02558_not_prime : ¬(recordGapCenter - 236332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236332]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02559_not_prime : ¬(recordGapCenter - 236250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236250]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

theorem fullRecordGapTerm02560_not_prime : ¬(recordGapCenter - 236212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236212]
  · apply fullRecordGapRow00010_fermat
    simp [fullRecordGapRow00010_values]

end PrimeFactorUnimodality
