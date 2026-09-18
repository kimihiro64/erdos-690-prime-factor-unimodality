import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00032_values : List Nat :=
  [fullRecordGapCenterValue + 464756,
    fullRecordGapCenterValue + 465162,
    fullRecordGapCenterValue + 465176,
    fullRecordGapCenterValue + 465242,
    fullRecordGapCenterValue + 465326,
    fullRecordGapCenterValue + 465342,
    fullRecordGapCenterValue + 465368,
    fullRecordGapCenterValue + 465398,
    fullRecordGapCenterValue + 465438,
    fullRecordGapCenterValue + 465512,
    fullRecordGapCenterValue + 465638,
    fullRecordGapCenterValue + 465722,
    fullRecordGapCenterValue + 465782,
    fullRecordGapCenterValue + 465788,
    fullRecordGapCenterValue + 465848,
    fullRecordGapCenterValue + 465882,
    fullRecordGapCenterValue + 465896,
    fullRecordGapCenterValue + 466028,
    fullRecordGapCenterValue + 466086,
    fullRecordGapCenterValue + 466266,
    fullRecordGapCenterValue + 466278,
    fullRecordGapCenterValue + 466338,
    fullRecordGapCenterValue + 466386,
    fullRecordGapCenterValue + 466442,
    fullRecordGapCenterValue + 466478,
    fullRecordGapCenterValue + 466482,
    fullRecordGapCenterValue + 466560,
    fullRecordGapCenterValue + 466566,
    fullRecordGapCenterValue + 466586,
    fullRecordGapCenterValue + 466652,
    fullRecordGapCenterValue + 466706,
    fullRecordGapCenterValue + 466782,
    fullRecordGapCenterValue + 466790,
    fullRecordGapCenterValue + 467156,
    fullRecordGapCenterValue + 467178,
    fullRecordGapCenterValue + 467202,
    fullRecordGapCenterValue + 467378,
    fullRecordGapCenterValue + 467426,
    fullRecordGapCenterValue + 467486,
    fullRecordGapCenterValue + 467510,
    fullRecordGapCenterValue + 467598,
    fullRecordGapCenterValue + 467706,
    fullRecordGapCenterValue + 467708,
    fullRecordGapCenterValue + 467822,
    fullRecordGapCenterValue + 467862,
    fullRecordGapCenterValue + 467876,
    fullRecordGapCenterValue + 467972,
    fullRecordGapCenterValue + 468042,
    fullRecordGapCenterValue + 468086,
    fullRecordGapCenterValue + 468242,
    fullRecordGapCenterValue + 468246,
    fullRecordGapCenterValue + 468290,
    fullRecordGapCenterValue + 468296,
    fullRecordGapCenterValue + 468386,
    fullRecordGapCenterValue + 468476,
    fullRecordGapCenterValue + 468542,
    fullRecordGapCenterValue + 468606,
    fullRecordGapCenterValue + 468632,
    fullRecordGapCenterValue + 468638,
    fullRecordGapCenterValue + 468686,
    fullRecordGapCenterValue + 468770,
    fullRecordGapCenterValue + 468822,
    fullRecordGapCenterValue + 468836,
    fullRecordGapCenterValue + 468890,
    fullRecordGapCenterValue + 468956,
    fullRecordGapCenterValue + 469002,
    fullRecordGapCenterValue + 469178,
    fullRecordGapCenterValue + 469226,
    fullRecordGapCenterValue + 469316,
    fullRecordGapCenterValue + 469466,
    fullRecordGapCenterValue + 469562,
    fullRecordGapCenterValue + 469598,
    fullRecordGapCenterValue + 469688,
    fullRecordGapCenterValue + 469698,
    fullRecordGapCenterValue + 469866,
    fullRecordGapCenterValue + 469922,
    fullRecordGapCenterValue + 469928,
    fullRecordGapCenterValue + 470012,
    fullRecordGapCenterValue + 470046,
    fullRecordGapCenterValue + 470082,
    fullRecordGapCenterValue + 470102,
    fullRecordGapCenterValue + 470138,
    fullRecordGapCenterValue + 470198,
    fullRecordGapCenterValue + 470222,
    fullRecordGapCenterValue + 470342,
    fullRecordGapCenterValue + 470486,
    fullRecordGapCenterValue + 470570,
    fullRecordGapCenterValue + 470636,
    fullRecordGapCenterValue + 470648,
    fullRecordGapCenterValue + 470870,
    fullRecordGapCenterValue + 470978,
    fullRecordGapCenterValue + 470982,
    fullRecordGapCenterValue + 471066,
    fullRecordGapCenterValue + 471110,
    fullRecordGapCenterValue + 471116,
    fullRecordGapCenterValue + 471182,
    fullRecordGapCenterValue + 471326,
    fullRecordGapCenterValue + 471332,
    fullRecordGapCenterValue + 471446,
    fullRecordGapCenterValue + 471578,
    fullRecordGapCenterValue + 471902,
    fullRecordGapCenterValue + 471908,
    fullRecordGapCenterValue + 472070,
    fullRecordGapCenterValue + 472106,
    fullRecordGapCenterValue + 472148,
    fullRecordGapCenterValue + 472286,
    fullRecordGapCenterValue + 472326,
    fullRecordGapCenterValue + 472418,
    fullRecordGapCenterValue + 472500,
    fullRecordGapCenterValue + 472586,
    fullRecordGapCenterValue + 472658,
    fullRecordGapCenterValue + 472818,
    fullRecordGapCenterValue + 472922,
    fullRecordGapCenterValue + 472938,
    fullRecordGapCenterValue + 472988,
    fullRecordGapCenterValue + 473006,
    fullRecordGapCenterValue + 473118,
    fullRecordGapCenterValue + 473126,
    fullRecordGapCenterValue + 473142,
    fullRecordGapCenterValue + 473322,
    fullRecordGapCenterValue + 473372,
    fullRecordGapCenterValue + 473498,
    fullRecordGapCenterValue + 473510,
    fullRecordGapCenterValue + 473576,
    fullRecordGapCenterValue + 473630,
    fullRecordGapCenterValue + 473768,
    fullRecordGapCenterValue + 473862,
    fullRecordGapCenterValue + 474038,
    fullRecordGapCenterValue + 474146,
    fullRecordGapCenterValue + 474170,
    fullRecordGapCenterValue + 474182,
    fullRecordGapCenterValue + 474248,
    fullRecordGapCenterValue + 474258,
    fullRecordGapCenterValue + 474302,
    fullRecordGapCenterValue + 474332,
    fullRecordGapCenterValue + 474378,
    fullRecordGapCenterValue + 474542,
    fullRecordGapCenterValue + 474590,
    fullRecordGapCenterValue + 474626,
    fullRecordGapCenterValue + 474686,
    fullRecordGapCenterValue + 474722,
    fullRecordGapCenterValue + 474836,
    fullRecordGapCenterValue + 474882,
    fullRecordGapCenterValue + 475028,
    fullRecordGapCenterValue + 475070,
    fullRecordGapCenterValue + 475142,
    fullRecordGapCenterValue + 475346,
    fullRecordGapCenterValue + 475352,
    fullRecordGapCenterValue + 475382,
    fullRecordGapCenterValue + 475638,
    fullRecordGapCenterValue + 475736,
    fullRecordGapCenterValue + 475802,
    fullRecordGapCenterValue + 475806,
    fullRecordGapCenterValue + 475868,
    fullRecordGapCenterValue + 475892,
    fullRecordGapCenterValue + 475998,
    fullRecordGapCenterValue + 476018,
    fullRecordGapCenterValue + 476072,
    fullRecordGapCenterValue + 476156,
    fullRecordGapCenterValue + 476198,
    fullRecordGapCenterValue + 476312,
    fullRecordGapCenterValue + 476348,
    fullRecordGapCenterValue + 476358,
    fullRecordGapCenterValue + 476390,
    fullRecordGapCenterValue + 476402,
    fullRecordGapCenterValue + 476466,
    fullRecordGapCenterValue + 476642,
    fullRecordGapCenterValue + 476936,
    fullRecordGapCenterValue + 476948,
    fullRecordGapCenterValue + 477038,
    fullRecordGapCenterValue + 477146,
    fullRecordGapCenterValue + 477170,
    fullRecordGapCenterValue + 477186,
    fullRecordGapCenterValue + 477278,
    fullRecordGapCenterValue + 477368,
    fullRecordGapCenterValue + 477446,
    fullRecordGapCenterValue + 477458,
    fullRecordGapCenterValue + 477656,
    fullRecordGapCenterValue + 477678,
    fullRecordGapCenterValue + 477716,
    fullRecordGapCenterValue + 477758,
    fullRecordGapCenterValue + 477762,
    fullRecordGapCenterValue + 477842,
    fullRecordGapCenterValue + 477878,
    fullRecordGapCenterValue + 477956,
    fullRecordGapCenterValue + 478070,
    fullRecordGapCenterValue + 478146,
    fullRecordGapCenterValue + 478158,
    fullRecordGapCenterValue + 478238,
    fullRecordGapCenterValue + 478370,
    fullRecordGapCenterValue + 478472,
    fullRecordGapCenterValue + 478658,
    fullRecordGapCenterValue + 478766,
    fullRecordGapCenterValue + 478796,
    fullRecordGapCenterValue + 478866,
    fullRecordGapCenterValue + 478938,
    fullRecordGapCenterValue + 479036,
    fullRecordGapCenterValue + 479078,
    fullRecordGapCenterValue + 479096,
    fullRecordGapCenterValue + 479238,
    fullRecordGapCenterValue + 479390,
    fullRecordGapCenterValue + 479418,
    fullRecordGapCenterValue + 479558,
    fullRecordGapCenterValue + 479768,
    fullRecordGapCenterValue + 479802,
    fullRecordGapCenterValue + 479810,
    fullRecordGapCenterValue + 480000,
    fullRecordGapCenterValue + 480068,
    fullRecordGapCenterValue + 480188,
    fullRecordGapCenterValue + 480218,
    fullRecordGapCenterValue + 480230,
    fullRecordGapCenterValue + 480296,
    fullRecordGapCenterValue + 480302,
    fullRecordGapCenterValue + 480306,
    fullRecordGapCenterValue + 480566,
    fullRecordGapCenterValue + 480642,
    fullRecordGapCenterValue + 480698,
    fullRecordGapCenterValue + 480728,
    fullRecordGapCenterValue + 480758,
    fullRecordGapCenterValue + 480846,
    fullRecordGapCenterValue + 480918,
    fullRecordGapCenterValue + 480932,
    fullRecordGapCenterValue + 481112,
    fullRecordGapCenterValue + 481142,
    fullRecordGapCenterValue + 481178,
    fullRecordGapCenterValue + 481196,
    fullRecordGapCenterValue + 481250,
    fullRecordGapCenterValue + 481310,
    fullRecordGapCenterValue + 481398,
    fullRecordGapCenterValue + 481478,
    fullRecordGapCenterValue + 481652,
    fullRecordGapCenterValue + 481706,
    fullRecordGapCenterValue + 481722,
    fullRecordGapCenterValue + 481736,
    fullRecordGapCenterValue + 481766,
    fullRecordGapCenterValue + 481790,
    fullRecordGapCenterValue + 482046,
    fullRecordGapCenterValue + 482168,
    fullRecordGapCenterValue + 482228,
    fullRecordGapCenterValue + 482252,
    fullRecordGapCenterValue + 482276,
    fullRecordGapCenterValue + 482322,
    fullRecordGapCenterValue + 482442,
    fullRecordGapCenterValue + 482606,
    fullRecordGapCenterValue + 482696,
    fullRecordGapCenterValue + 482756,
    fullRecordGapCenterValue + 482826,
    fullRecordGapCenterValue + 482858,
    fullRecordGapCenterValue + 482882,
    fullRecordGapCenterValue + 482906,
    fullRecordGapCenterValue + 482946,
    fullRecordGapCenterValue + 482948,
    fullRecordGapCenterValue + 482990,
    fullRecordGapCenterValue + 483068,
    fullRecordGapCenterValue + 483078,
    fullRecordGapCenterValue + 483122]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00032_fermat : ∀ n ∈ fullRecordGapRow00032_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm07937_not_prime : ¬(recordGapCenter + 464756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 464756]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07938_not_prime : ¬(recordGapCenter + 465162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465162]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07939_not_prime : ¬(recordGapCenter + 465176).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465176]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07940_not_prime : ¬(recordGapCenter + 465242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465242]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07941_not_prime : ¬(recordGapCenter + 465326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465326]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07942_not_prime : ¬(recordGapCenter + 465342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465342]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07943_not_prime : ¬(recordGapCenter + 465368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465368]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07944_not_prime : ¬(recordGapCenter + 465398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465398]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07945_not_prime : ¬(recordGapCenter + 465438).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465438]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07946_not_prime : ¬(recordGapCenter + 465512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465512]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07947_not_prime : ¬(recordGapCenter + 465638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465638]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07948_not_prime : ¬(recordGapCenter + 465722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465722]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07949_not_prime : ¬(recordGapCenter + 465782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465782]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07950_not_prime : ¬(recordGapCenter + 465788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465788]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07951_not_prime : ¬(recordGapCenter + 465848).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465848]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07952_not_prime : ¬(recordGapCenter + 465882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465882]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07953_not_prime : ¬(recordGapCenter + 465896).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 465896]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07954_not_prime : ¬(recordGapCenter + 466028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466028]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07955_not_prime : ¬(recordGapCenter + 466086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466086]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07956_not_prime : ¬(recordGapCenter + 466266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466266]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07957_not_prime : ¬(recordGapCenter + 466278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466278]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07958_not_prime : ¬(recordGapCenter + 466338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466338]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07959_not_prime : ¬(recordGapCenter + 466386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466386]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07960_not_prime : ¬(recordGapCenter + 466442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466442]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07961_not_prime : ¬(recordGapCenter + 466478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466478]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07962_not_prime : ¬(recordGapCenter + 466482).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466482]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07963_not_prime : ¬(recordGapCenter + 466560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466560]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07964_not_prime : ¬(recordGapCenter + 466566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466566]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07965_not_prime : ¬(recordGapCenter + 466586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466586]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07966_not_prime : ¬(recordGapCenter + 466652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466652]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07967_not_prime : ¬(recordGapCenter + 466706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466706]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07968_not_prime : ¬(recordGapCenter + 466782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466782]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07969_not_prime : ¬(recordGapCenter + 466790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 466790]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07970_not_prime : ¬(recordGapCenter + 467156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467156]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07971_not_prime : ¬(recordGapCenter + 467178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467178]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07972_not_prime : ¬(recordGapCenter + 467202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467202]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07973_not_prime : ¬(recordGapCenter + 467378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467378]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07974_not_prime : ¬(recordGapCenter + 467426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467426]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07975_not_prime : ¬(recordGapCenter + 467486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467486]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07976_not_prime : ¬(recordGapCenter + 467510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467510]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07977_not_prime : ¬(recordGapCenter + 467598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467598]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07978_not_prime : ¬(recordGapCenter + 467706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467706]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07979_not_prime : ¬(recordGapCenter + 467708).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467708]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07980_not_prime : ¬(recordGapCenter + 467822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467822]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07981_not_prime : ¬(recordGapCenter + 467862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467862]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07982_not_prime : ¬(recordGapCenter + 467876).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467876]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07983_not_prime : ¬(recordGapCenter + 467972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 467972]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07984_not_prime : ¬(recordGapCenter + 468042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468042]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07985_not_prime : ¬(recordGapCenter + 468086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468086]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07986_not_prime : ¬(recordGapCenter + 468242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468242]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07987_not_prime : ¬(recordGapCenter + 468246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468246]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07988_not_prime : ¬(recordGapCenter + 468290).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468290]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07989_not_prime : ¬(recordGapCenter + 468296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468296]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07990_not_prime : ¬(recordGapCenter + 468386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468386]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07991_not_prime : ¬(recordGapCenter + 468476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468476]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07992_not_prime : ¬(recordGapCenter + 468542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468542]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07993_not_prime : ¬(recordGapCenter + 468606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468606]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07994_not_prime : ¬(recordGapCenter + 468632).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468632]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07995_not_prime : ¬(recordGapCenter + 468638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468638]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07996_not_prime : ¬(recordGapCenter + 468686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468686]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07997_not_prime : ¬(recordGapCenter + 468770).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468770]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07998_not_prime : ¬(recordGapCenter + 468822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468822]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm07999_not_prime : ¬(recordGapCenter + 468836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468836]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08000_not_prime : ¬(recordGapCenter + 468890).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468890]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08001_not_prime : ¬(recordGapCenter + 468956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 468956]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08002_not_prime : ¬(recordGapCenter + 469002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469002]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08003_not_prime : ¬(recordGapCenter + 469178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469178]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08004_not_prime : ¬(recordGapCenter + 469226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469226]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08005_not_prime : ¬(recordGapCenter + 469316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469316]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08006_not_prime : ¬(recordGapCenter + 469466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469466]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08007_not_prime : ¬(recordGapCenter + 469562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469562]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08008_not_prime : ¬(recordGapCenter + 469598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469598]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08009_not_prime : ¬(recordGapCenter + 469688).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469688]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08010_not_prime : ¬(recordGapCenter + 469698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469698]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08011_not_prime : ¬(recordGapCenter + 469866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469866]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08012_not_prime : ¬(recordGapCenter + 469922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469922]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08013_not_prime : ¬(recordGapCenter + 469928).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 469928]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08014_not_prime : ¬(recordGapCenter + 470012).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470012]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08015_not_prime : ¬(recordGapCenter + 470046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470046]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08016_not_prime : ¬(recordGapCenter + 470082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470082]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08017_not_prime : ¬(recordGapCenter + 470102).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470102]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08018_not_prime : ¬(recordGapCenter + 470138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470138]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08019_not_prime : ¬(recordGapCenter + 470198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470198]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08020_not_prime : ¬(recordGapCenter + 470222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470222]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08021_not_prime : ¬(recordGapCenter + 470342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470342]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08022_not_prime : ¬(recordGapCenter + 470486).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470486]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08023_not_prime : ¬(recordGapCenter + 470570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470570]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08024_not_prime : ¬(recordGapCenter + 470636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470636]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08025_not_prime : ¬(recordGapCenter + 470648).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470648]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08026_not_prime : ¬(recordGapCenter + 470870).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470870]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08027_not_prime : ¬(recordGapCenter + 470978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470978]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08028_not_prime : ¬(recordGapCenter + 470982).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 470982]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08029_not_prime : ¬(recordGapCenter + 471066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471066]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08030_not_prime : ¬(recordGapCenter + 471110).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471110]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08031_not_prime : ¬(recordGapCenter + 471116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471116]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08032_not_prime : ¬(recordGapCenter + 471182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471182]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08033_not_prime : ¬(recordGapCenter + 471326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471326]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08034_not_prime : ¬(recordGapCenter + 471332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471332]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08035_not_prime : ¬(recordGapCenter + 471446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471446]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08036_not_prime : ¬(recordGapCenter + 471578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471578]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08037_not_prime : ¬(recordGapCenter + 471902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471902]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08038_not_prime : ¬(recordGapCenter + 471908).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 471908]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08039_not_prime : ¬(recordGapCenter + 472070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472070]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08040_not_prime : ¬(recordGapCenter + 472106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472106]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08041_not_prime : ¬(recordGapCenter + 472148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472148]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08042_not_prime : ¬(recordGapCenter + 472286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472286]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08043_not_prime : ¬(recordGapCenter + 472326).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472326]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08044_not_prime : ¬(recordGapCenter + 472418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472418]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08045_not_prime : ¬(recordGapCenter + 472500).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472500]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08046_not_prime : ¬(recordGapCenter + 472586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472586]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08047_not_prime : ¬(recordGapCenter + 472658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472658]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08048_not_prime : ¬(recordGapCenter + 472818).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472818]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08049_not_prime : ¬(recordGapCenter + 472922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472922]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08050_not_prime : ¬(recordGapCenter + 472938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472938]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08051_not_prime : ¬(recordGapCenter + 472988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 472988]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08052_not_prime : ¬(recordGapCenter + 473006).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473006]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08053_not_prime : ¬(recordGapCenter + 473118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473118]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08054_not_prime : ¬(recordGapCenter + 473126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473126]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08055_not_prime : ¬(recordGapCenter + 473142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473142]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08056_not_prime : ¬(recordGapCenter + 473322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473322]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08057_not_prime : ¬(recordGapCenter + 473372).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473372]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08058_not_prime : ¬(recordGapCenter + 473498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473498]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08059_not_prime : ¬(recordGapCenter + 473510).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473510]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08060_not_prime : ¬(recordGapCenter + 473576).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473576]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08061_not_prime : ¬(recordGapCenter + 473630).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473630]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08062_not_prime : ¬(recordGapCenter + 473768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473768]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08063_not_prime : ¬(recordGapCenter + 473862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 473862]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08064_not_prime : ¬(recordGapCenter + 474038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474038]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08065_not_prime : ¬(recordGapCenter + 474146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474146]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08066_not_prime : ¬(recordGapCenter + 474170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474170]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08067_not_prime : ¬(recordGapCenter + 474182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474182]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08068_not_prime : ¬(recordGapCenter + 474248).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474248]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08069_not_prime : ¬(recordGapCenter + 474258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474258]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08070_not_prime : ¬(recordGapCenter + 474302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474302]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08071_not_prime : ¬(recordGapCenter + 474332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474332]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08072_not_prime : ¬(recordGapCenter + 474378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474378]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08073_not_prime : ¬(recordGapCenter + 474542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474542]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08074_not_prime : ¬(recordGapCenter + 474590).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474590]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08075_not_prime : ¬(recordGapCenter + 474626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474626]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08076_not_prime : ¬(recordGapCenter + 474686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474686]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08077_not_prime : ¬(recordGapCenter + 474722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474722]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08078_not_prime : ¬(recordGapCenter + 474836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474836]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08079_not_prime : ¬(recordGapCenter + 474882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 474882]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08080_not_prime : ¬(recordGapCenter + 475028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475028]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08081_not_prime : ¬(recordGapCenter + 475070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475070]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08082_not_prime : ¬(recordGapCenter + 475142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475142]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08083_not_prime : ¬(recordGapCenter + 475346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475346]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08084_not_prime : ¬(recordGapCenter + 475352).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475352]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08085_not_prime : ¬(recordGapCenter + 475382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475382]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08086_not_prime : ¬(recordGapCenter + 475638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475638]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08087_not_prime : ¬(recordGapCenter + 475736).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475736]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08088_not_prime : ¬(recordGapCenter + 475802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475802]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08089_not_prime : ¬(recordGapCenter + 475806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475806]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08090_not_prime : ¬(recordGapCenter + 475868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475868]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08091_not_prime : ¬(recordGapCenter + 475892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475892]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08092_not_prime : ¬(recordGapCenter + 475998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 475998]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08093_not_prime : ¬(recordGapCenter + 476018).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476018]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08094_not_prime : ¬(recordGapCenter + 476072).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476072]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08095_not_prime : ¬(recordGapCenter + 476156).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476156]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08096_not_prime : ¬(recordGapCenter + 476198).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476198]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08097_not_prime : ¬(recordGapCenter + 476312).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476312]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08098_not_prime : ¬(recordGapCenter + 476348).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476348]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08099_not_prime : ¬(recordGapCenter + 476358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476358]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08100_not_prime : ¬(recordGapCenter + 476390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476390]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08101_not_prime : ¬(recordGapCenter + 476402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476402]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08102_not_prime : ¬(recordGapCenter + 476466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476466]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08103_not_prime : ¬(recordGapCenter + 476642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476642]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08104_not_prime : ¬(recordGapCenter + 476936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476936]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08105_not_prime : ¬(recordGapCenter + 476948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 476948]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08106_not_prime : ¬(recordGapCenter + 477038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477038]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08107_not_prime : ¬(recordGapCenter + 477146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477146]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08108_not_prime : ¬(recordGapCenter + 477170).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477170]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08109_not_prime : ¬(recordGapCenter + 477186).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477186]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08110_not_prime : ¬(recordGapCenter + 477278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477278]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08111_not_prime : ¬(recordGapCenter + 477368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477368]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08112_not_prime : ¬(recordGapCenter + 477446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477446]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08113_not_prime : ¬(recordGapCenter + 477458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477458]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08114_not_prime : ¬(recordGapCenter + 477656).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477656]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08115_not_prime : ¬(recordGapCenter + 477678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477678]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08116_not_prime : ¬(recordGapCenter + 477716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477716]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08117_not_prime : ¬(recordGapCenter + 477758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477758]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08118_not_prime : ¬(recordGapCenter + 477762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477762]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08119_not_prime : ¬(recordGapCenter + 477842).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477842]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08120_not_prime : ¬(recordGapCenter + 477878).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477878]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08121_not_prime : ¬(recordGapCenter + 477956).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 477956]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08122_not_prime : ¬(recordGapCenter + 478070).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478070]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08123_not_prime : ¬(recordGapCenter + 478146).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478146]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08124_not_prime : ¬(recordGapCenter + 478158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478158]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08125_not_prime : ¬(recordGapCenter + 478238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478238]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08126_not_prime : ¬(recordGapCenter + 478370).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478370]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08127_not_prime : ¬(recordGapCenter + 478472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478472]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08128_not_prime : ¬(recordGapCenter + 478658).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478658]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08129_not_prime : ¬(recordGapCenter + 478766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478766]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08130_not_prime : ¬(recordGapCenter + 478796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478796]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08131_not_prime : ¬(recordGapCenter + 478866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478866]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08132_not_prime : ¬(recordGapCenter + 478938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 478938]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08133_not_prime : ¬(recordGapCenter + 479036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479036]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08134_not_prime : ¬(recordGapCenter + 479078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479078]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08135_not_prime : ¬(recordGapCenter + 479096).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479096]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08136_not_prime : ¬(recordGapCenter + 479238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479238]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08137_not_prime : ¬(recordGapCenter + 479390).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479390]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08138_not_prime : ¬(recordGapCenter + 479418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479418]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08139_not_prime : ¬(recordGapCenter + 479558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479558]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08140_not_prime : ¬(recordGapCenter + 479768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479768]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08141_not_prime : ¬(recordGapCenter + 479802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479802]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08142_not_prime : ¬(recordGapCenter + 479810).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 479810]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08143_not_prime : ¬(recordGapCenter + 480000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480000]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08144_not_prime : ¬(recordGapCenter + 480068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480068]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08145_not_prime : ¬(recordGapCenter + 480188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480188]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08146_not_prime : ¬(recordGapCenter + 480218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480218]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08147_not_prime : ¬(recordGapCenter + 480230).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480230]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08148_not_prime : ¬(recordGapCenter + 480296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480296]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08149_not_prime : ¬(recordGapCenter + 480302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480302]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08150_not_prime : ¬(recordGapCenter + 480306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480306]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08151_not_prime : ¬(recordGapCenter + 480566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480566]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08152_not_prime : ¬(recordGapCenter + 480642).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480642]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08153_not_prime : ¬(recordGapCenter + 480698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480698]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08154_not_prime : ¬(recordGapCenter + 480728).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480728]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08155_not_prime : ¬(recordGapCenter + 480758).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480758]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08156_not_prime : ¬(recordGapCenter + 480846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480846]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08157_not_prime : ¬(recordGapCenter + 480918).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480918]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08158_not_prime : ¬(recordGapCenter + 480932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 480932]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08159_not_prime : ¬(recordGapCenter + 481112).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481112]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08160_not_prime : ¬(recordGapCenter + 481142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481142]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08161_not_prime : ¬(recordGapCenter + 481178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481178]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08162_not_prime : ¬(recordGapCenter + 481196).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481196]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08163_not_prime : ¬(recordGapCenter + 481250).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481250]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08164_not_prime : ¬(recordGapCenter + 481310).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481310]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08165_not_prime : ¬(recordGapCenter + 481398).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481398]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08166_not_prime : ¬(recordGapCenter + 481478).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481478]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08167_not_prime : ¬(recordGapCenter + 481652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481652]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08168_not_prime : ¬(recordGapCenter + 481706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481706]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08169_not_prime : ¬(recordGapCenter + 481722).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481722]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08170_not_prime : ¬(recordGapCenter + 481736).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481736]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08171_not_prime : ¬(recordGapCenter + 481766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481766]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08172_not_prime : ¬(recordGapCenter + 481790).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 481790]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08173_not_prime : ¬(recordGapCenter + 482046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482046]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08174_not_prime : ¬(recordGapCenter + 482168).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482168]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08175_not_prime : ¬(recordGapCenter + 482228).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482228]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08176_not_prime : ¬(recordGapCenter + 482252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482252]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08177_not_prime : ¬(recordGapCenter + 482276).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482276]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08178_not_prime : ¬(recordGapCenter + 482322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482322]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08179_not_prime : ¬(recordGapCenter + 482442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482442]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08180_not_prime : ¬(recordGapCenter + 482606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482606]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08181_not_prime : ¬(recordGapCenter + 482696).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482696]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08182_not_prime : ¬(recordGapCenter + 482756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482756]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08183_not_prime : ¬(recordGapCenter + 482826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482826]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08184_not_prime : ¬(recordGapCenter + 482858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482858]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08185_not_prime : ¬(recordGapCenter + 482882).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482882]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08186_not_prime : ¬(recordGapCenter + 482906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482906]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08187_not_prime : ¬(recordGapCenter + 482946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482946]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08188_not_prime : ¬(recordGapCenter + 482948).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482948]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08189_not_prime : ¬(recordGapCenter + 482990).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 482990]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08190_not_prime : ¬(recordGapCenter + 483068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483068]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08191_not_prime : ¬(recordGapCenter + 483078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483078]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

theorem fullRecordGapTerm08192_not_prime : ¬(recordGapCenter + 483122).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 483122]
  · apply fullRecordGapRow00032_fermat
    simp [fullRecordGapRow00032_values]

end PrimeFactorUnimodality
