import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00011_values : List Nat :=
  [fullRecordGapCenterValue - 236122,
    fullRecordGapCenterValue - 236092,
    fullRecordGapCenterValue - 236044,
    fullRecordGapCenterValue - 235918,
    fullRecordGapCenterValue - 235678,
    fullRecordGapCenterValue - 235618,
    fullRecordGapCenterValue - 235594,
    fullRecordGapCenterValue - 235402,
    fullRecordGapCenterValue - 235200,
    fullRecordGapCenterValue - 234862,
    fullRecordGapCenterValue - 234772,
    fullRecordGapCenterValue - 234748,
    fullRecordGapCenterValue - 234742,
    fullRecordGapCenterValue - 234538,
    fullRecordGapCenterValue - 234478,
    fullRecordGapCenterValue - 234418,
    fullRecordGapCenterValue - 234202,
    fullRecordGapCenterValue - 234148,
    fullRecordGapCenterValue - 233698,
    fullRecordGapCenterValue - 233638,
    fullRecordGapCenterValue - 233572,
    fullRecordGapCenterValue - 233452,
    fullRecordGapCenterValue - 233284,
    fullRecordGapCenterValue - 233074,
    fullRecordGapCenterValue - 233062,
    fullRecordGapCenterValue - 232822,
    fullRecordGapCenterValue - 232612,
    fullRecordGapCenterValue - 232444,
    fullRecordGapCenterValue - 232402,
    fullRecordGapCenterValue - 232378,
    fullRecordGapCenterValue - 232320,
    fullRecordGapCenterValue - 232054,
    fullRecordGapCenterValue - 231964,
    fullRecordGapCenterValue - 231892,
    fullRecordGapCenterValue - 231802,
    fullRecordGapCenterValue - 231772,
    fullRecordGapCenterValue - 231754,
    fullRecordGapCenterValue - 231718,
    fullRecordGapCenterValue - 231622,
    fullRecordGapCenterValue - 231604,
    fullRecordGapCenterValue - 231562,
    fullRecordGapCenterValue - 231454,
    fullRecordGapCenterValue - 231412,
    fullRecordGapCenterValue - 231388,
    fullRecordGapCenterValue - 231178,
    fullRecordGapCenterValue - 231172,
    fullRecordGapCenterValue - 231142,
    fullRecordGapCenterValue - 231094,
    fullRecordGapCenterValue - 230638,
    fullRecordGapCenterValue - 230302,
    fullRecordGapCenterValue - 230134,
    fullRecordGapCenterValue - 229654,
    fullRecordGapCenterValue - 229324,
    fullRecordGapCenterValue - 229198,
    fullRecordGapCenterValue - 228934,
    fullRecordGapCenterValue - 228690,
    fullRecordGapCenterValue - 228658,
    fullRecordGapCenterValue - 228622,
    fullRecordGapCenterValue - 228598,
    fullRecordGapCenterValue - 228442,
    fullRecordGapCenterValue - 228388,
    fullRecordGapCenterValue - 228322,
    fullRecordGapCenterValue - 227938,
    fullRecordGapCenterValue - 227782,
    fullRecordGapCenterValue - 227692,
    fullRecordGapCenterValue - 227674,
    fullRecordGapCenterValue - 227434,
    fullRecordGapCenterValue - 227428,
    fullRecordGapCenterValue - 227182,
    fullRecordGapCenterValue - 227134,
    fullRecordGapCenterValue - 227092,
    fullRecordGapCenterValue - 227068,
    fullRecordGapCenterValue - 227002,
    fullRecordGapCenterValue - 226558,
    fullRecordGapCenterValue - 226294,
    fullRecordGapCenterValue - 226222,
    fullRecordGapCenterValue - 226162,
    fullRecordGapCenterValue - 226102,
    fullRecordGapCenterValue - 226078,
    fullRecordGapCenterValue - 226042,
    fullRecordGapCenterValue - 226012,
    fullRecordGapCenterValue - 225994,
    fullRecordGapCenterValue - 225868,
    fullRecordGapCenterValue - 225748,
    fullRecordGapCenterValue - 225718,
    fullRecordGapCenterValue - 225598,
    fullRecordGapCenterValue - 225532,
    fullRecordGapCenterValue - 225514,
    fullRecordGapCenterValue - 225154,
    fullRecordGapCenterValue - 225118,
    fullRecordGapCenterValue - 225000,
    fullRecordGapCenterValue - 224788,
    fullRecordGapCenterValue - 224674,
    fullRecordGapCenterValue - 224662,
    fullRecordGapCenterValue - 224524,
    fullRecordGapCenterValue - 224494,
    fullRecordGapCenterValue - 224398,
    fullRecordGapCenterValue - 224362,
    fullRecordGapCenterValue - 224278,
    fullRecordGapCenterValue - 224212,
    fullRecordGapCenterValue - 224194,
    fullRecordGapCenterValue - 224164,
    fullRecordGapCenterValue - 224038,
    fullRecordGapCenterValue - 223918,
    fullRecordGapCenterValue - 223732,
    fullRecordGapCenterValue - 223654,
    fullRecordGapCenterValue - 223582,
    fullRecordGapCenterValue - 223318,
    fullRecordGapCenterValue - 223228,
    fullRecordGapCenterValue - 223078,
    fullRecordGapCenterValue - 222934,
    fullRecordGapCenterValue - 222862,
    fullRecordGapCenterValue - 222694,
    fullRecordGapCenterValue - 222652,
    fullRecordGapCenterValue - 222532,
    fullRecordGapCenterValue - 222484,
    fullRecordGapCenterValue - 222238,
    fullRecordGapCenterValue - 222058,
    fullRecordGapCenterValue - 222004,
    fullRecordGapCenterValue - 221902,
    fullRecordGapCenterValue - 221842,
    fullRecordGapCenterValue - 221758,
    fullRecordGapCenterValue - 221644,
    fullRecordGapCenterValue - 221458,
    fullRecordGapCenterValue - 221332,
    fullRecordGapCenterValue - 221218,
    fullRecordGapCenterValue - 221164,
    fullRecordGapCenterValue - 220882,
    fullRecordGapCenterValue - 220828,
    fullRecordGapCenterValue - 220678,
    fullRecordGapCenterValue - 220468,
    fullRecordGapCenterValue - 220138,
    fullRecordGapCenterValue - 220084,
    fullRecordGapCenterValue - 220078,
    fullRecordGapCenterValue - 220000,
    fullRecordGapCenterValue - 219874,
    fullRecordGapCenterValue - 219694,
    fullRecordGapCenterValue - 219658,
    fullRecordGapCenterValue - 219508,
    fullRecordGapCenterValue - 219238,
    fullRecordGapCenterValue - 219148,
    fullRecordGapCenterValue - 219034,
    fullRecordGapCenterValue - 219004,
    fullRecordGapCenterValue - 218908,
    fullRecordGapCenterValue - 218700,
    fullRecordGapCenterValue - 218668,
    fullRecordGapCenterValue - 218458,
    fullRecordGapCenterValue - 218404,
    fullRecordGapCenterValue - 218308,
    fullRecordGapCenterValue - 218242,
    fullRecordGapCenterValue - 218188,
    fullRecordGapCenterValue - 217942,
    fullRecordGapCenterValue - 217774,
    fullRecordGapCenterValue - 217762,
    fullRecordGapCenterValue - 217654,
    fullRecordGapCenterValue - 217468,
    fullRecordGapCenterValue - 217354,
    fullRecordGapCenterValue - 217324,
    fullRecordGapCenterValue - 217174,
    fullRecordGapCenterValue - 217114,
    fullRecordGapCenterValue - 217108,
    fullRecordGapCenterValue - 216922,
    fullRecordGapCenterValue - 216772,
    fullRecordGapCenterValue - 216382,
    fullRecordGapCenterValue - 216358,
    fullRecordGapCenterValue - 216262,
    fullRecordGapCenterValue - 216214,
    fullRecordGapCenterValue - 216090,
    fullRecordGapCenterValue - 216082,
    fullRecordGapCenterValue - 216052,
    fullRecordGapCenterValue - 216004,
    fullRecordGapCenterValue - 215854,
    fullRecordGapCenterValue - 215794,
    fullRecordGapCenterValue - 215674,
    fullRecordGapCenterValue - 215668,
    fullRecordGapCenterValue - 215554,
    fullRecordGapCenterValue - 215374,
    fullRecordGapCenterValue - 214924,
    fullRecordGapCenterValue - 214678,
    fullRecordGapCenterValue - 214612,
    fullRecordGapCenterValue - 214492,
    fullRecordGapCenterValue - 214342,
    fullRecordGapCenterValue - 214114,
    fullRecordGapCenterValue - 213814,
    fullRecordGapCenterValue - 213748,
    fullRecordGapCenterValue - 213628,
    fullRecordGapCenterValue - 213574,
    fullRecordGapCenterValue - 213562,
    fullRecordGapCenterValue - 213444,
    fullRecordGapCenterValue - 213442,
    fullRecordGapCenterValue - 213412,
    fullRecordGapCenterValue - 213292,
    fullRecordGapCenterValue - 213274,
    fullRecordGapCenterValue - 213082,
    fullRecordGapCenterValue - 212974,
    fullRecordGapCenterValue - 212782,
    fullRecordGapCenterValue - 212698,
    fullRecordGapCenterValue - 212662,
    fullRecordGapCenterValue - 212434,
    fullRecordGapCenterValue - 212404,
    fullRecordGapCenterValue - 212242,
    fullRecordGapCenterValue - 212218,
    fullRecordGapCenterValue - 211942,
    fullRecordGapCenterValue - 211852,
    fullRecordGapCenterValue - 211804,
    fullRecordGapCenterValue - 211750,
    fullRecordGapCenterValue - 211680,
    fullRecordGapCenterValue - 211612,
    fullRecordGapCenterValue - 211348,
    fullRecordGapCenterValue - 211054,
    fullRecordGapCenterValue - 210814,
    fullRecordGapCenterValue - 210802,
    fullRecordGapCenterValue - 210718,
    fullRecordGapCenterValue - 210682,
    fullRecordGapCenterValue - 210502,
    fullRecordGapCenterValue - 210244,
    fullRecordGapCenterValue - 210142,
    fullRecordGapCenterValue - 210004,
    fullRecordGapCenterValue - 209758,
    fullRecordGapCenterValue - 209548,
    fullRecordGapCenterValue - 209452,
    fullRecordGapCenterValue - 209122,
    fullRecordGapCenterValue - 209088,
    fullRecordGapCenterValue - 208918,
    fullRecordGapCenterValue - 208834,
    fullRecordGapCenterValue - 208738,
    fullRecordGapCenterValue - 208708,
    fullRecordGapCenterValue - 208612,
    fullRecordGapCenterValue - 208414,
    fullRecordGapCenterValue - 208324,
    fullRecordGapCenterValue - 208228,
    fullRecordGapCenterValue - 208204,
    fullRecordGapCenterValue - 208084,
    fullRecordGapCenterValue - 208018,
    fullRecordGapCenterValue - 207982,
    fullRecordGapCenterValue - 207934,
    fullRecordGapCenterValue - 207900,
    fullRecordGapCenterValue - 207682,
    fullRecordGapCenterValue - 207652,
    fullRecordGapCenterValue - 207412,
    fullRecordGapCenterValue - 207268,
    fullRecordGapCenterValue - 207238,
    fullRecordGapCenterValue - 207058,
    fullRecordGapCenterValue - 206902,
    fullRecordGapCenterValue - 206842,
    fullRecordGapCenterValue - 206818,
    fullRecordGapCenterValue - 206698,
    fullRecordGapCenterValue - 206638,
    fullRecordGapCenterValue - 206614,
    fullRecordGapCenterValue - 206308,
    fullRecordGapCenterValue - 206250,
    fullRecordGapCenterValue - 206098,
    fullRecordGapCenterValue - 206068,
    fullRecordGapCenterValue - 206014,
    fullRecordGapCenterValue - 205522,
    fullRecordGapCenterValue - 205228]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00011_fermat : ∀ n ∈ fullRecordGapRow00011_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02561_not_prime : ¬(recordGapCenter - 236122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236122]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02562_not_prime : ¬(recordGapCenter - 236092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236092]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02563_not_prime : ¬(recordGapCenter - 236044).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 236044]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02564_not_prime : ¬(recordGapCenter - 235918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 235918]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02565_not_prime : ¬(recordGapCenter - 235678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 235678]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02566_not_prime : ¬(recordGapCenter - 235618).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 235618]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02567_not_prime : ¬(recordGapCenter - 235594).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 235594]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02568_not_prime : ¬(recordGapCenter - 235402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 235402]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02569_not_prime : ¬(recordGapCenter - 235200).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 235200]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02570_not_prime : ¬(recordGapCenter - 234862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234862]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02571_not_prime : ¬(recordGapCenter - 234772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234772]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02572_not_prime : ¬(recordGapCenter - 234748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234748]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02573_not_prime : ¬(recordGapCenter - 234742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234742]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02574_not_prime : ¬(recordGapCenter - 234538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234538]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02575_not_prime : ¬(recordGapCenter - 234478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234478]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02576_not_prime : ¬(recordGapCenter - 234418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234418]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02577_not_prime : ¬(recordGapCenter - 234202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234202]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02578_not_prime : ¬(recordGapCenter - 234148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 234148]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02579_not_prime : ¬(recordGapCenter - 233698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 233698]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02580_not_prime : ¬(recordGapCenter - 233638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 233638]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02581_not_prime : ¬(recordGapCenter - 233572).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 233572]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02582_not_prime : ¬(recordGapCenter - 233452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 233452]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02583_not_prime : ¬(recordGapCenter - 233284).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 233284]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02584_not_prime : ¬(recordGapCenter - 233074).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 233074]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02585_not_prime : ¬(recordGapCenter - 233062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 233062]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02586_not_prime : ¬(recordGapCenter - 232822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 232822]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02587_not_prime : ¬(recordGapCenter - 232612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 232612]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02588_not_prime : ¬(recordGapCenter - 232444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 232444]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02589_not_prime : ¬(recordGapCenter - 232402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 232402]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02590_not_prime : ¬(recordGapCenter - 232378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 232378]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02591_not_prime : ¬(recordGapCenter - 232320).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 232320]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02592_not_prime : ¬(recordGapCenter - 232054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 232054]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02593_not_prime : ¬(recordGapCenter - 231964).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231964]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02594_not_prime : ¬(recordGapCenter - 231892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231892]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02595_not_prime : ¬(recordGapCenter - 231802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231802]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02596_not_prime : ¬(recordGapCenter - 231772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231772]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02597_not_prime : ¬(recordGapCenter - 231754).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231754]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02598_not_prime : ¬(recordGapCenter - 231718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231718]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02599_not_prime : ¬(recordGapCenter - 231622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231622]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02600_not_prime : ¬(recordGapCenter - 231604).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231604]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02601_not_prime : ¬(recordGapCenter - 231562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231562]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02602_not_prime : ¬(recordGapCenter - 231454).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231454]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02603_not_prime : ¬(recordGapCenter - 231412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231412]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02604_not_prime : ¬(recordGapCenter - 231388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231388]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02605_not_prime : ¬(recordGapCenter - 231178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231178]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02606_not_prime : ¬(recordGapCenter - 231172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231172]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02607_not_prime : ¬(recordGapCenter - 231142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231142]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02608_not_prime : ¬(recordGapCenter - 231094).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 231094]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02609_not_prime : ¬(recordGapCenter - 230638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 230638]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02610_not_prime : ¬(recordGapCenter - 230302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 230302]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02611_not_prime : ¬(recordGapCenter - 230134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 230134]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02612_not_prime : ¬(recordGapCenter - 229654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 229654]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02613_not_prime : ¬(recordGapCenter - 229324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 229324]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02614_not_prime : ¬(recordGapCenter - 229198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 229198]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02615_not_prime : ¬(recordGapCenter - 228934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228934]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02616_not_prime : ¬(recordGapCenter - 228690).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228690]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02617_not_prime : ¬(recordGapCenter - 228658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228658]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02618_not_prime : ¬(recordGapCenter - 228622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228622]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02619_not_prime : ¬(recordGapCenter - 228598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228598]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02620_not_prime : ¬(recordGapCenter - 228442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228442]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02621_not_prime : ¬(recordGapCenter - 228388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228388]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02622_not_prime : ¬(recordGapCenter - 228322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 228322]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02623_not_prime : ¬(recordGapCenter - 227938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227938]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02624_not_prime : ¬(recordGapCenter - 227782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227782]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02625_not_prime : ¬(recordGapCenter - 227692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227692]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02626_not_prime : ¬(recordGapCenter - 227674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227674]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02627_not_prime : ¬(recordGapCenter - 227434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227434]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02628_not_prime : ¬(recordGapCenter - 227428).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227428]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02629_not_prime : ¬(recordGapCenter - 227182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227182]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02630_not_prime : ¬(recordGapCenter - 227134).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227134]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02631_not_prime : ¬(recordGapCenter - 227092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227092]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02632_not_prime : ¬(recordGapCenter - 227068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227068]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02633_not_prime : ¬(recordGapCenter - 227002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 227002]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02634_not_prime : ¬(recordGapCenter - 226558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226558]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02635_not_prime : ¬(recordGapCenter - 226294).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226294]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02636_not_prime : ¬(recordGapCenter - 226222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226222]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02637_not_prime : ¬(recordGapCenter - 226162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226162]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02638_not_prime : ¬(recordGapCenter - 226102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226102]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02639_not_prime : ¬(recordGapCenter - 226078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226078]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02640_not_prime : ¬(recordGapCenter - 226042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226042]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02641_not_prime : ¬(recordGapCenter - 226012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 226012]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02642_not_prime : ¬(recordGapCenter - 225994).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225994]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02643_not_prime : ¬(recordGapCenter - 225868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225868]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02644_not_prime : ¬(recordGapCenter - 225748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225748]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02645_not_prime : ¬(recordGapCenter - 225718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225718]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02646_not_prime : ¬(recordGapCenter - 225598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225598]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02647_not_prime : ¬(recordGapCenter - 225532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225532]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02648_not_prime : ¬(recordGapCenter - 225514).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225514]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02649_not_prime : ¬(recordGapCenter - 225154).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225154]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02650_not_prime : ¬(recordGapCenter - 225118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225118]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02651_not_prime : ¬(recordGapCenter - 225000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 225000]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02652_not_prime : ¬(recordGapCenter - 224788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224788]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02653_not_prime : ¬(recordGapCenter - 224674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224674]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02654_not_prime : ¬(recordGapCenter - 224662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224662]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02655_not_prime : ¬(recordGapCenter - 224524).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224524]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02656_not_prime : ¬(recordGapCenter - 224494).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224494]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02657_not_prime : ¬(recordGapCenter - 224398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224398]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02658_not_prime : ¬(recordGapCenter - 224362).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224362]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02659_not_prime : ¬(recordGapCenter - 224278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224278]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02660_not_prime : ¬(recordGapCenter - 224212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224212]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02661_not_prime : ¬(recordGapCenter - 224194).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224194]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02662_not_prime : ¬(recordGapCenter - 224164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224164]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02663_not_prime : ¬(recordGapCenter - 224038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 224038]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02664_not_prime : ¬(recordGapCenter - 223918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 223918]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02665_not_prime : ¬(recordGapCenter - 223732).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 223732]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02666_not_prime : ¬(recordGapCenter - 223654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 223654]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02667_not_prime : ¬(recordGapCenter - 223582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 223582]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02668_not_prime : ¬(recordGapCenter - 223318).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 223318]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02669_not_prime : ¬(recordGapCenter - 223228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 223228]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02670_not_prime : ¬(recordGapCenter - 223078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 223078]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02671_not_prime : ¬(recordGapCenter - 222934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222934]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02672_not_prime : ¬(recordGapCenter - 222862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222862]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02673_not_prime : ¬(recordGapCenter - 222694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222694]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02674_not_prime : ¬(recordGapCenter - 222652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222652]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02675_not_prime : ¬(recordGapCenter - 222532).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222532]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02676_not_prime : ¬(recordGapCenter - 222484).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222484]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02677_not_prime : ¬(recordGapCenter - 222238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222238]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02678_not_prime : ¬(recordGapCenter - 222058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222058]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02679_not_prime : ¬(recordGapCenter - 222004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 222004]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02680_not_prime : ¬(recordGapCenter - 221902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221902]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02681_not_prime : ¬(recordGapCenter - 221842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221842]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02682_not_prime : ¬(recordGapCenter - 221758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221758]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02683_not_prime : ¬(recordGapCenter - 221644).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221644]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02684_not_prime : ¬(recordGapCenter - 221458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221458]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02685_not_prime : ¬(recordGapCenter - 221332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221332]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02686_not_prime : ¬(recordGapCenter - 221218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221218]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02687_not_prime : ¬(recordGapCenter - 221164).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 221164]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02688_not_prime : ¬(recordGapCenter - 220882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220882]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02689_not_prime : ¬(recordGapCenter - 220828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220828]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02690_not_prime : ¬(recordGapCenter - 220678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220678]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02691_not_prime : ¬(recordGapCenter - 220468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220468]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02692_not_prime : ¬(recordGapCenter - 220138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220138]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02693_not_prime : ¬(recordGapCenter - 220084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220084]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02694_not_prime : ¬(recordGapCenter - 220078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220078]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02695_not_prime : ¬(recordGapCenter - 220000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 220000]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02696_not_prime : ¬(recordGapCenter - 219874).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219874]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02697_not_prime : ¬(recordGapCenter - 219694).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219694]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02698_not_prime : ¬(recordGapCenter - 219658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219658]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02699_not_prime : ¬(recordGapCenter - 219508).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219508]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02700_not_prime : ¬(recordGapCenter - 219238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219238]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02701_not_prime : ¬(recordGapCenter - 219148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219148]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02702_not_prime : ¬(recordGapCenter - 219034).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219034]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02703_not_prime : ¬(recordGapCenter - 219004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 219004]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02704_not_prime : ¬(recordGapCenter - 218908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218908]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02705_not_prime : ¬(recordGapCenter - 218700).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218700]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02706_not_prime : ¬(recordGapCenter - 218668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218668]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02707_not_prime : ¬(recordGapCenter - 218458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218458]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02708_not_prime : ¬(recordGapCenter - 218404).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218404]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02709_not_prime : ¬(recordGapCenter - 218308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218308]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02710_not_prime : ¬(recordGapCenter - 218242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218242]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02711_not_prime : ¬(recordGapCenter - 218188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 218188]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02712_not_prime : ¬(recordGapCenter - 217942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217942]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02713_not_prime : ¬(recordGapCenter - 217774).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217774]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02714_not_prime : ¬(recordGapCenter - 217762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217762]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02715_not_prime : ¬(recordGapCenter - 217654).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217654]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02716_not_prime : ¬(recordGapCenter - 217468).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217468]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02717_not_prime : ¬(recordGapCenter - 217354).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217354]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02718_not_prime : ¬(recordGapCenter - 217324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217324]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02719_not_prime : ¬(recordGapCenter - 217174).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217174]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02720_not_prime : ¬(recordGapCenter - 217114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217114]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02721_not_prime : ¬(recordGapCenter - 217108).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 217108]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02722_not_prime : ¬(recordGapCenter - 216922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216922]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02723_not_prime : ¬(recordGapCenter - 216772).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216772]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02724_not_prime : ¬(recordGapCenter - 216382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216382]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02725_not_prime : ¬(recordGapCenter - 216358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216358]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02726_not_prime : ¬(recordGapCenter - 216262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216262]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02727_not_prime : ¬(recordGapCenter - 216214).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216214]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02728_not_prime : ¬(recordGapCenter - 216090).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216090]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02729_not_prime : ¬(recordGapCenter - 216082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216082]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02730_not_prime : ¬(recordGapCenter - 216052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216052]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02731_not_prime : ¬(recordGapCenter - 216004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 216004]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02732_not_prime : ¬(recordGapCenter - 215854).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 215854]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02733_not_prime : ¬(recordGapCenter - 215794).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 215794]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02734_not_prime : ¬(recordGapCenter - 215674).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 215674]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02735_not_prime : ¬(recordGapCenter - 215668).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 215668]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02736_not_prime : ¬(recordGapCenter - 215554).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 215554]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02737_not_prime : ¬(recordGapCenter - 215374).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 215374]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02738_not_prime : ¬(recordGapCenter - 214924).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 214924]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02739_not_prime : ¬(recordGapCenter - 214678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 214678]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02740_not_prime : ¬(recordGapCenter - 214612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 214612]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02741_not_prime : ¬(recordGapCenter - 214492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 214492]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02742_not_prime : ¬(recordGapCenter - 214342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 214342]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02743_not_prime : ¬(recordGapCenter - 214114).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 214114]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02744_not_prime : ¬(recordGapCenter - 213814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213814]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02745_not_prime : ¬(recordGapCenter - 213748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213748]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02746_not_prime : ¬(recordGapCenter - 213628).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213628]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02747_not_prime : ¬(recordGapCenter - 213574).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213574]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02748_not_prime : ¬(recordGapCenter - 213562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213562]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02749_not_prime : ¬(recordGapCenter - 213444).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213444]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02750_not_prime : ¬(recordGapCenter - 213442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213442]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02751_not_prime : ¬(recordGapCenter - 213412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213412]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02752_not_prime : ¬(recordGapCenter - 213292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213292]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02753_not_prime : ¬(recordGapCenter - 213274).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213274]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02754_not_prime : ¬(recordGapCenter - 213082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 213082]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02755_not_prime : ¬(recordGapCenter - 212974).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212974]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02756_not_prime : ¬(recordGapCenter - 212782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212782]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02757_not_prime : ¬(recordGapCenter - 212698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212698]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02758_not_prime : ¬(recordGapCenter - 212662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212662]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02759_not_prime : ¬(recordGapCenter - 212434).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212434]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02760_not_prime : ¬(recordGapCenter - 212404).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212404]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02761_not_prime : ¬(recordGapCenter - 212242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212242]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02762_not_prime : ¬(recordGapCenter - 212218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 212218]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02763_not_prime : ¬(recordGapCenter - 211942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211942]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02764_not_prime : ¬(recordGapCenter - 211852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211852]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02765_not_prime : ¬(recordGapCenter - 211804).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211804]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02766_not_prime : ¬(recordGapCenter - 211750).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211750]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02767_not_prime : ¬(recordGapCenter - 211680).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211680]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02768_not_prime : ¬(recordGapCenter - 211612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211612]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02769_not_prime : ¬(recordGapCenter - 211348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211348]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02770_not_prime : ¬(recordGapCenter - 211054).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 211054]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02771_not_prime : ¬(recordGapCenter - 210814).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210814]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02772_not_prime : ¬(recordGapCenter - 210802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210802]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02773_not_prime : ¬(recordGapCenter - 210718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210718]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02774_not_prime : ¬(recordGapCenter - 210682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210682]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02775_not_prime : ¬(recordGapCenter - 210502).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210502]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02776_not_prime : ¬(recordGapCenter - 210244).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210244]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02777_not_prime : ¬(recordGapCenter - 210142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210142]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02778_not_prime : ¬(recordGapCenter - 210004).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 210004]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02779_not_prime : ¬(recordGapCenter - 209758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 209758]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02780_not_prime : ¬(recordGapCenter - 209548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 209548]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02781_not_prime : ¬(recordGapCenter - 209452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 209452]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02782_not_prime : ¬(recordGapCenter - 209122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 209122]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02783_not_prime : ¬(recordGapCenter - 209088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 209088]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02784_not_prime : ¬(recordGapCenter - 208918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208918]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02785_not_prime : ¬(recordGapCenter - 208834).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208834]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02786_not_prime : ¬(recordGapCenter - 208738).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208738]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02787_not_prime : ¬(recordGapCenter - 208708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208708]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02788_not_prime : ¬(recordGapCenter - 208612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208612]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02789_not_prime : ¬(recordGapCenter - 208414).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208414]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02790_not_prime : ¬(recordGapCenter - 208324).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208324]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02791_not_prime : ¬(recordGapCenter - 208228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208228]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02792_not_prime : ¬(recordGapCenter - 208204).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208204]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02793_not_prime : ¬(recordGapCenter - 208084).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208084]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02794_not_prime : ¬(recordGapCenter - 208018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 208018]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02795_not_prime : ¬(recordGapCenter - 207982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207982]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02796_not_prime : ¬(recordGapCenter - 207934).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207934]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02797_not_prime : ¬(recordGapCenter - 207900).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207900]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02798_not_prime : ¬(recordGapCenter - 207682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207682]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02799_not_prime : ¬(recordGapCenter - 207652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207652]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02800_not_prime : ¬(recordGapCenter - 207412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207412]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02801_not_prime : ¬(recordGapCenter - 207268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207268]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02802_not_prime : ¬(recordGapCenter - 207238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207238]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02803_not_prime : ¬(recordGapCenter - 207058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 207058]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02804_not_prime : ¬(recordGapCenter - 206902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206902]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02805_not_prime : ¬(recordGapCenter - 206842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206842]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02806_not_prime : ¬(recordGapCenter - 206818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206818]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02807_not_prime : ¬(recordGapCenter - 206698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206698]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02808_not_prime : ¬(recordGapCenter - 206638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206638]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02809_not_prime : ¬(recordGapCenter - 206614).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206614]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02810_not_prime : ¬(recordGapCenter - 206308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206308]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02811_not_prime : ¬(recordGapCenter - 206250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206250]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02812_not_prime : ¬(recordGapCenter - 206098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206098]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02813_not_prime : ¬(recordGapCenter - 206068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206068]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02814_not_prime : ¬(recordGapCenter - 206014).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 206014]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02815_not_prime : ¬(recordGapCenter - 205522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 205522]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

theorem fullRecordGapTerm02816_not_prime : ¬(recordGapCenter - 205228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue - 205228]
  · apply fullRecordGapRow00011_fermat
    simp [fullRecordGapRow00011_values]

end PrimeFactorUnimodality
